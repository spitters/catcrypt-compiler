/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.CTRegions
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall

@[expose] public section

set_option autoImplicit false

/-!
# The region analysis across a call of a linked callee

`RegionSep.memCheck` refuses a `call`. This module adds a call arm to the region analysis
for a caller whose calls are answered by a callee that restores `%rsp`, keeps the
registers outside a clobber set `clob` and writes no byte outside the `G` bytes below its
entry stack register (`RegionSep.CallPres`). The abstract effect of the call
(`RegionSep.transCall`) keeps the stack offset, drops the facts on clobbered registers and
the zero-flag fact, and keeps a stack-word fact only for a word at or above the caller's
stack register, which neither the return-address word written by
`LprogBytesDecode.callOps` nor the callee's footprint overlaps.

The inference `RegionSep.inferMX` of the region certificate and `RegionSep.inferX` of the
constant-time certificate carry the call arm. The certificate checks and the constant-time
decision on them are in `Haxc.CTRegionsCallOut`.

## Main results

* `RegionSep.transCall_sound`: the abstract effect of a call describes the state after the
  stack operations of the call, the callee and the return.
* `RegionSep.transCallO_sound`: the same for a callee that also writes an out region inside a
  static window of the caller's frame (`RegionSep.CallPresO`), whose effect
  `RegionSep.transCallO` also drops the stack-word facts meeting the window.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT

namespace RegionSep

/-! ## 1. The abstract effect of a call -/

/-- The stack word at offset `e` lies at or above the stack offset `sp`, at most
    `2 ^ 64 - 16 - G` above it: outside the return-address word and the `G` bytes below
    it. -/
def keptSlot (G : Nat) (sp e : Int) : Bool :=
  decide (sp ≤ e) && decide (e - sp + 16 + G ≤ 2 ^ 64)

/-- **The abstract effect of a call** of a callee with clobber set `clob` and footprint in
    the `G` bytes below its entry stack register: the facts on clobbered registers, the
    zero-flag fact and the stack-word facts below the stack register are dropped. -/
def transCall (G : Nat) (clob : String → Bool) (m : MA) : MA :=
  { sp := m.sp
    ent := m.ent.filter fun p => !clob p.1
    zero := m.zero.filter fun r => !clob r
    slot := m.slot.filter fun e => keptSlot G m.sp e.1
    le := m.le.filter fun f => !clob f.1 && !clob f.2.1
    nz := m.nz.filter fun r => !clob r
    zf := none
    cst := m.cst.filter fun p => !clob p.1
    w := (m.w.keepRegs fun x => !clob x).keepWords (keptSlot G m.sp) }

/-- What a callee entered in `sc0` and returning in `sc` preserves: `%rsp`, the registers
    outside `clob`, and every byte outside the `G` bytes below the entry stack register. -/
structure CallPres (clob : String → Bool) (G : Nat) (sc0 sc : AState) : Prop where
  rsp : sc.regs "%rsp" = sc0.regs "%rsp"
  keep : ∀ x, clob x = false → sc.regs x = sc0.regs x
  frame : ∀ x, ¬ InFrame (sc0.regs "%rsp") G x → sc.mem x = sc0.mem x

/-- A run of the guarded callee `guarded c X` of a specified callee preserves what
    `CallPres` states, for a clobber set `clob` covering `c.clob` and a footprint in the
    `G` bytes below the entry stack register. -/
theorem callPres_of_guarded {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {clob : String → Bool} (hclob : ∀ x, clob x = false → c.clob x = false) {G : Nat}
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x) {sc0 sc : AState}
    {t : List CTLeak} (h : guarded c X sc0 t sc) : CallPres clob G sc0 sc :=
  ⟨hX.rsp _ _ _ h.1 h.2, fun x hx => hX.keep _ _ _ h.1 h.2 x (hclob x hx),
    fun x hx => hX.frame _ _ _ h.1 h.2 x fun hf => hx (hfoot _ _ hf)⟩

theorem callOps_rsp (sa : AState) (n : Nat) :
    (runBlockA sa (callOps n)).regs "%rsp" = sa.regs "%rsp" + BitVec.ofInt 64 (-8) := by
  simp [callOps, evalInstrA, evalInstr, JState.setReg, JState.get, x86_LEA, AState.view]

theorem callOps_regs (sa : AState) (n : Nat) {x : String} (hx : x ≠ "%rsp") :
    (runBlockA sa (callOps n)).regs x = sa.regs x := by
  simp only [callOps, runBlockA_cons, runBlockA_nil]
  rw [evalInstrA_regs_of_not_dst _ _ _ (by simp [dstRegs]),
    evalInstrA_regs_of_not_dst _ _ _ (by simp [dstRegs, hx])]

theorem callOps_read64 (sa : AState) (n : Nat) {b : BitVec 64}
    (hb : Disjoint8 (sa.regs "%rsp" + BitVec.ofInt 64 (-8)) b) :
    read64 (runBlockA sa (callOps n)).mem b = read64 sa.mem b := by
  have hr := evalInstrA_rsp_lea sa "%rsp" (-8)
  simp only [callOps, runBlockA_cons, runBlockA_nil]
  simp only [evalInstrA, writeAddr] at hr ⊢
  rw [read64_write64_of_disjoint _ _ _ _ (by simpa [hr] using hb)]

theorem retOps_rsp (sc : AState) :
    (runBlockA sc retOps).regs "%rsp" = sc.regs "%rsp" + BitVec.ofInt 64 8 := by
  simp only [retOps, runBlockA_cons, runBlockA_nil]
  exact evalInstrA_rsp_lea sc "%rsp" 8

theorem retOps_regs (sc : AState) {x : String} (hx : x ≠ "%rsp") :
    (runBlockA sc retOps).regs x = sc.regs x := by
  simp only [retOps, runBlockA_cons, runBlockA_nil]
  exact evalInstrA_regs_of_not_dst _ _ _ (by simp [dstRegs, hx])

theorem retOps_mem (sc : AState) : (runBlockA sc retOps).mem = sc.mem := by
  simp [retOps, evalInstrA, writeAddr]

/-- Two memories that agree on the eight bytes from `a` give the same word at `a`. -/
theorem read64_congr {m₁ m₂ : AMem} {a : BitVec 64}
    (h : ∀ x, InRange8 a x → m₁ x = m₂ x) : read64 m₁ a = read64 m₂ a := by
  have hk : ∀ k, k < 8 → m₁ (a + BitVec.ofNat 64 k) = m₂ (a + BitVec.ofNat 64 k) :=
    fun k hk => h _ (by unfold InRange8; simp; omega)
  have h0 : m₁ a = m₂ a := by simpa using hk 0 (by decide)
  simp only [read64, h0, hk 1 (by decide), hk 2 (by decide), hk 3 (by decide),
    hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

section Soundness

variable {σ : AbiLayout} {s0 : AState}

/-- **Soundness of the abstract effect of a call.** If `m` describes the caller's state
    `sa` and the callee entered after the stack operations of the call returns in `sc`
    with `CallPres clob G`, then `transCall G clob m` describes the state after the
    return. -/
theorem transCall_sound {G : Nat} {clob : String → Bool} {m : MA} {sa sc : AState} {n : Nat}
    (hI : Inv σ s0 m sa) (hP : CallPres clob G (runBlockA sa (callOps n)) sc) :
    Inv σ s0 (transCall G clob m) (runBlockA sc retOps) := by
  set sc0 := runBlockA sa (callOps n) with hsc0
  have hsp : (runBlockA sc retOps).regs "%rsp" = sa.regs "%rsp" := by
    rw [retOps_rsp, hP.rsp, hsc0, callOps_rsp, ofInt_add_assoc]
    simp
  have hreg : ∀ x, clob x = false → (runBlockA sc retOps).regs x = sa.regs x := by
    intro x hx
    by_cases hr : x = "%rsp"
    · subst hr; exact hsp
    · rw [retOps_regs _ hr, hP.keep x hx, hsc0, callOps_regs _ _ hr]
  have hreg' : ∀ x, (!clob x) = true → (runBlockA sc retOps).regs x = sa.regs x :=
    fun x hx => hreg x (by simpa using hx)
  have hword : ∀ e, keptSlot G m.sp e = true → inW σ e = true →
      wdAt s0 (runBlockA sc retOps) e = wdAt s0 sa e := by
    intro e hk _
    simp only [keptSlot, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨h1, h2⟩ := hk
    have hrsp0 : sc0.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
        + BitVec.ofInt 64 (-8) := by
      rw [hsc0, callOps_rsp, hI.sp]
    have haddr : s0.regs "%rsp" + BitVec.ofInt 64 e
        = sc0.regs "%rsp" + BitVec.ofInt 64 (e - m.sp + 8) := by
      rw [hrsp0, ofInt_add_assoc, ofInt_add_assoc]
      congr 2
      omega
    simp only [wdAt]
    rw [retOps_mem, haddr]
    have hm : ∀ x, InRange8 (sc0.regs "%rsp" + BitVec.ofInt 64 (e - m.sp + 8)) x →
        sc.mem x = sc0.mem x := fun x hx =>
      hP.frame x (not_inFrame_of_inRange8 (by omega) (by omega) hx)
    rw [read64_congr hm, ← haddr, hsc0, callOps_read64]
    rw [hI.sp, ofInt_add_assoc]
    exact disjoint8_add_ofInt (s0.regs "%rsp") (m.sp + -8) e (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hI.w.frame hreg' hword⟩
  · rw [hsp]; exact hI.sp
  · intro p hp
    simp only [transCall, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.ent p hp.1
  · intro r hr
    simp only [transCall, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.zero r hr.1
  · intro e he
    simp only [transCall, List.mem_filter, keptSlot, Bool.and_eq_true,
      decide_eq_true_eq] at he
    obtain ⟨he, h1, h2⟩ := he
    refine ⟨(hI.slot e he).1, ?_⟩
    have hrsp0 : sc0.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
        + BitVec.ofInt 64 (-8) := by
      rw [hsc0, callOps_rsp, hI.sp]
    have haddr : s0.regs "%rsp" + BitVec.ofInt 64 e.1
        = sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8) := by
      rw [hrsp0, ofInt_add_assoc, ofInt_add_assoc]
      congr 2
      omega
    rw [retOps_mem, haddr]
    have hm : ∀ x, InRange8 (sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8)) x →
        sc.mem x = sc0.mem x := fun x hx =>
      hP.frame x (not_inFrame_of_inRange8 (by omega) (by omega) hx)
    rw [read64_congr hm, ← haddr, hsc0, callOps_read64]
    · exact (hI.slot e he).2
    · rw [hI.sp, ofInt_add_assoc]
      exact disjoint8_add_ofInt (s0.regs "%rsp") (m.sp + -8) e.1 (by omega) (by omega)
  · intro f hf
    simp only [transCall, List.mem_filter, Bool.and_eq_true] at hf
    rw [hreg' _ hf.2.1, hreg' _ hf.2.2]; exact hI.le f hf.1
  · intro r hr
    simp only [transCall, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.nz r hr.1
  · intro c hc
    simp [transCall] at hc
  · intro p hp
    simp only [transCall, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.cst p hp.1

end Soundness

/-! ## 1a. A call that writes an out array of the caller's frame -/

/-- The stack word at offset `e` lies outside the window of `len` words from the offset
    `sp + lo`. -/
def outWin (sp lo : Int) (len : Nat) (e : Int) : Bool :=
  decide (e + 8 ≤ sp + lo) || decide (sp + lo + 8 * len ≤ e)

/-- **The abstract effect of a call with an out array** of `w.2` words at the offset `w.1`
    above the caller's stack register: `transCall G clob m` without the stack-word facts
    that meet the window of the array. -/
def transCallO (G : Nat) (clob : String → Bool) (w : Int × Nat) (m : MA) : MA :=
  { sp := m.sp
    ent := m.ent.filter fun p => !clob p.1
    zero := m.zero.filter fun r => !clob r
    slot := m.slot.filter fun e => keptSlot G m.sp e.1 && outWin m.sp w.1 w.2 e.1
    le := m.le.filter fun f => !clob f.1 && !clob f.2.1
    nz := m.nz.filter fun r => !clob r
    zf := none
    cst := m.cst.filter fun p => !clob p.1 }

/-- What a callee entered in `sc0` and returning in `sc` preserves when it writes the out
    region `O sc0`: `%rsp`, the registers outside `clob`, and every byte outside the `G`
    bytes below the entry stack register and outside `O sc0`. -/
structure CallPresO (clob : String → Bool) (G : Nat) (O : AState → BitVec 64 → Prop)
    (sc0 sc : AState) : Prop where
  rsp : sc.regs "%rsp" = sc0.regs "%rsp"
  keep : ∀ x, clob x = false → sc.regs x = sc0.regs x
  frame : ∀ x, ¬ InFrame (sc0.regs "%rsp") G x → ¬ O sc0 x → sc.mem x = sc0.mem x

/-- A run of the guarded callee `guarded c X` of a specified callee whose footprint lies in
    the `G` bytes below the entry stack register or in the out region `O` preserves what
    `CallPresO` states, for a clobber set `clob` covering `c.clob`. -/
theorem callPresO_of_guarded {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {clob : String → Bool} (hclob : ∀ x, clob x = false → c.clob x = false) {G : Nat}
    {O : AState → BitVec 64 → Prop}
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x ∨ O s x) {sc0 sc : AState}
    {t : List CTLeak} (h : guarded c X sc0 t sc) : CallPresO clob G O sc0 sc :=
  ⟨hX.rsp _ _ _ h.1 h.2, fun x hx => hX.keep _ _ _ h.1 h.2 x (hclob x hx),
    fun x hx hO => hX.frame _ _ _ h.1 h.2 x fun hf => (hfoot _ _ hf).elim hx hO⟩

/-- A byte of the word at offset `d ≥ 0` above `a` lies outside the window of `len` words
    at offset `lo ≥ 0` above `a` when the two ranges are disjoint and below `2 ^ 64`. -/
theorem not_inWin_of_inRange8 {a x : BitVec 64} {d lo : Int} {len : Nat} (hd : 0 ≤ d)
    (hd8 : d + 8 ≤ 2 ^ 64) (hlo : 0 ≤ lo) (hlen : lo + 8 * len ≤ 2 ^ 64)
    (hk : d + 8 ≤ lo ∨ lo + 8 * len ≤ d) (hx : InRange8 (a + BitVec.ofInt 64 d) x) :
    ¬ (x - (a + BitVec.ofInt 64 lo)).toNat < 8 * len := by
  unfold InRange8 at hx
  have := a.isLt
  have := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hx ⊢
  omega

section Soundness

variable {σ : AbiLayout} {s0 : AState}

/-- **Soundness of the abstract effect of a call with an out array.** If `m` describes the
    caller's state `sa`, the callee entered after the stack operations of the call returns
    in `sc` with `CallPresO clob G O`, and the out region lies in the window of `len` words
    at the offset `lo` above the caller's stack register, with `0 ≤ lo` and
    `lo + 8 * len ≤ 2 ^ 64`, then `transCallO G clob (lo, len) m` describes the state after
    the return. -/
theorem transCallO_sound {G : Nat} {clob : String → Bool} {O : AState → BitVec 64 → Prop}
    {m : MA} {sa sc : AState} {n : Nat} {lo : Int} {len : Nat}
    (hI : Inv σ s0 m sa) (hP : CallPresO clob G O (runBlockA sa (callOps n)) sc)
    (hlo : 0 ≤ lo) (hlen : lo + 8 * len ≤ 2 ^ 64)
    (hOW : ∀ x, O (runBlockA sa (callOps n)) x →
      (x - (sa.regs "%rsp" + BitVec.ofInt 64 lo)).toNat < 8 * len) :
    Inv σ s0 (transCallO G clob (lo, len) m) (runBlockA sc retOps) := by
  set sc0 := runBlockA sa (callOps n) with hsc0
  have hsp : (runBlockA sc retOps).regs "%rsp" = sa.regs "%rsp" := by
    rw [retOps_rsp, hP.rsp, hsc0, callOps_rsp, ofInt_add_assoc]
    simp
  have hreg : ∀ x, clob x = false → (runBlockA sc retOps).regs x = sa.regs x := by
    intro x hx
    by_cases hr : x = "%rsp"
    · subst hr; exact hsp
    · rw [retOps_regs _ hr, hP.keep x hx, hsc0, callOps_regs _ _ hr]
  have hreg' : ∀ x, (!clob x) = true → (runBlockA sc retOps).regs x = sa.regs x :=
    fun x hx => hreg x (by simpa using hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨by simp [transCallO], by simp [transCallO],
    by simp [transCallO], by simp [transCallO], by simp [transCallO], by simp [transCallO]⟩⟩
  · rw [hsp]; exact hI.sp
  · intro p hp
    simp only [transCallO, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.ent p hp.1
  · intro r hr
    simp only [transCallO, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.zero r hr.1
  · intro e he
    simp only [transCallO, List.mem_filter, keptSlot, outWin, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq] at he
    obtain ⟨he, ⟨h1, h2⟩, h3⟩ := he
    refine ⟨(hI.slot e he).1, ?_⟩
    have hrsp0 : sc0.regs "%rsp" = s0.regs "%rsp" + BitVec.ofInt 64 m.sp
        + BitVec.ofInt 64 (-8) := by
      rw [hsc0, callOps_rsp, hI.sp]
    have haddr : s0.regs "%rsp" + BitVec.ofInt 64 e.1
        = sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8) := by
      rw [hrsp0, ofInt_add_assoc, ofInt_add_assoc]
      congr 2
      omega
    have hcaller : sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8)
        = sa.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp) := by
      rw [hsc0, callOps_rsp, ofInt_add_assoc]
      congr 2
      omega
    rw [retOps_mem, haddr]
    have hm : ∀ x, InRange8 (sc0.regs "%rsp" + BitVec.ofInt 64 (e.1 - m.sp + 8)) x →
        sc.mem x = sc0.mem x := fun x hx =>
      hP.frame x (not_inFrame_of_inRange8 (by omega) (by omega) hx) fun hO =>
        not_inWin_of_inRange8 (by omega) (by omega) hlo hlen (by omega)
          (hcaller ▸ hx) (hOW x hO)
    rw [read64_congr hm, ← haddr, hsc0, callOps_read64]
    · exact (hI.slot e he).2
    · rw [hI.sp, ofInt_add_assoc]
      exact disjoint8_add_ofInt (s0.regs "%rsp") (m.sp + -8) e.1 (by omega) (by omega)
  · intro f hf
    simp only [transCallO, List.mem_filter, Bool.and_eq_true] at hf
    rw [hreg' _ hf.2.1, hreg' _ hf.2.2]; exact hI.le f hf.1
  · intro r hr
    simp only [transCallO, List.mem_filter] at hr
    rw [hreg' _ hr.2]; exact hI.nz r hr.1
  · intro c hc
    simp [transCallO] at hc
  · intro p hp
    simp only [transCallO, List.mem_filter] at hp
    rw [hreg' _ hp.2]; exact hI.cst p hp.1

end Soundness

/-! ## 2. Inference of the region certificate with a call arm -/

/-- One forward sweep of the region analysis with the call arm. -/
def sweepMX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr)
    (M : Array (Option MA)) : Array (Option MA) × Bool :=
  (List.range prog.length).foldl (fun (acc : Array (Option MA) × Bool) pc =>
    match acc.1.getD pc none, prog[pc]? with
    | some m, some (.op i) =>
        match trans σ m i with
        | some o => let r := meetIntoM acc.1 (pc + 1) o; (r.1, acc.2 || r.2)
        | none => acc
    | some m, some (.jcc cc t) =>
        match condtOfNibble cc with
        | some c =>
            let r1 := meetIntoM acc.1 t (jccOut m c true)
            let r2 := meetIntoM r1.1 (pc + 1) (jccOut m c false)
            (r2.1, acc.2 || r1.2 || r2.2)
        | none => acc
    | some m, some (.call _) =>
        let r := meetIntoM acc.1 (pc + 1) (transCall G clob m); (r.1, acc.2 || r.2)
    | _, _ => acc) (M, false)

/-- Sweeps until no change, at most `n` times. -/
def fixMX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    Nat → Array (Option MA) → Array (Option MA)
  | 0, M => M
  | n + 1, M =>
    let r := sweepMX σ clob G prog M
    if r.2 then fixMX σ clob G prog n r.1 else r.1

/-- The inferred certificate of the region analysis with the call arm. -/
def inferMX (σ : AbiLayout) (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    Array (Option MA) :=
  fixMX σ clob G prog (prog.length + 2)
    ((Array.replicate prog.length none).set! 0 (some (init σ)))

/-! ## 3. Inference of the constant-time certificate with a call arm -/

/-- The offset `q` above the callee's entry stack register lies outside its `G`-byte
    footprint: `0 ≤ q` and `q + 8 + G ≤ 2 ^ 64`. -/
def qOk (G : Nat) (q : Int) : Bool := decide (0 ≤ q) && decide (q + 8 + G ≤ 2 ^ 64)

/-- The part of the public set `a` a call of a callee with clobber set `clob` and footprint
    in `G` bytes keeps: `%rsp`, the registers outside `clob`, and the frame words whose
    callee offset passes `qOk G`, apart from the return-address word. -/
def keepX (clob : String → Bool) (G : Nat) (a : PubA) : PubA :=
  ⟨a.regs.filter (fun x => x == "%rsp" || !clob x),
    a.cells.filter (fun c => qOk G (c + 8) && far (c + 8) 0), false, []⟩

/-- The successors of index `pc` with their public sets, following `checkAtX`. -/
def succsX (clob : String → Bool) (G : Nat) (prog : List RInstr) (pc : Nat) (a : PubA) :
    List (Nat × PubA) :=
  match prog[pc]? with
  | some (.op i) => [(pc + 1, stepA a i)]
  | some (.jcc _ t) => [(t, a), (pc + 1, a)]
  | some (.push x) => [(pc + 1, stepBlock a (pushOps x))]
  | some (.pop x) => [(pc + 1, stepBlock a (popOps x))]
  | some (.call _) => [(pc + 1, keepX clob G a)]
  | _ => []

/-- Meet the public set `b` into the certificate at index `s`, reporting a change. -/
def meetIntoX (A : List (Option PubA)) (s : Nat) (b : PubA) : List (Option PubA) × Bool :=
  let o := meetO (certAt A s) b
  if s < A.length ∧ certAt A s ≠ o then (A.set s o, true) else (A, false)

/-- One forward sweep of the constant-time analysis with the call arm. -/
def sweepX (clob : String → Bool) (G : Nat) (prog : List RInstr) (A : List (Option PubA)) :
    List (Option PubA) × Bool :=
  (List.range prog.length).foldl (fun (acc : List (Option PubA) × Bool) pc =>
    match certAt acc.1 pc with
    | none => acc
    | some a => (succsX clob G prog pc a).foldl (fun (acc : List (Option PubA) × Bool) so =>
        let r := meetIntoX acc.1 so.1 so.2; (r.1, acc.2 || r.2)) acc) (A, false)

/-- Sweeps until no change, at most `n` times. -/
def fixX (clob : String → Bool) (G : Nat) (prog : List RInstr) :
    Nat → List (Option PubA) → List (Option PubA)
  | 0, A => A
  | n + 1, A =>
    let r := sweepX clob G prog A
    if r.2 then fixX clob G prog n r.1 else r.1

/-- The inferred constant-time certificate with the call arm, from the entry set `P`. -/
def inferX (clob : String → Bool) (G : Nat) (prog : List RInstr) (P : PubA) :
    List (Option PubA) :=
  fixX clob G prog (prog.length + 2) ((List.replicate prog.length none).set 0 (some P))

/-- The certificate `A` with each frame word kept when it lies inside the frame range of
    `σ` at every stack offset of `sps`. -/
def trimCertL (σ : AbiLayout) (sps : List Int) (A : List (Option PubA)) :
    List (Option PubA) :=
  A.map (Option.map fun a =>
    { a with cells := a.cells.filter (fun o => sps.all (fun sp => inW σ (sp + o))) })

/-- The registers of the certificate `A` outside `clob`. -/
def keptRegsX (clob : String → Bool) (A : List (Option PubA)) : List String :=
  (A.flatMap fun o => match o with
    | some a => a.regs
    | none => []).filter fun x => !clob x

/-- The callee offsets `c + 8` of the frame words of `A` that pass `qOk G`. -/
def keptCellsX (G : Nat) (A : List (Option PubA)) : List Int :=
  ((certCells A).map (· + 8)).filter (qOk G)

end RegionSep

end CatCrypt.Crypto.SecureCompilation.Haxc
