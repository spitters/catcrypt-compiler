/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
public import CatCrypt.Crypto.SecureCompilation.CT.Leakage
public import CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertStraight

@[expose] public section

/-!
# The valued leakage of the flag machine

The leakage of the flag machine `lsemFuelMemF` in the events `CTLeak` of the `LprogLeakCT`
model. An instruction emits:

* for each array operand of an `Lopn`, an address event at the array base: the
  compile-time offset of `.arr b i`, and for `.arrIdx b x sc` the scale `sc` times the value
  the index register `x` holds in the register file;
* for a flag-reading conditional (`flagCondCC?`), the branch event of the decision the flag
  machine takes, `zf` against the polarity of the condition code;
* for a register conditional, the branch event of its test `condNZ`;
* nothing otherwise.

`lsemFuelMemFLeak P fuel s` runs `P` as `lsemFuelMemF` does and returns the final state with
the list of events in execution order. `MemFCT P pubEq` is constant time of `P` in the
relational form `ConstantTimeRel` over the terminating runs.

The leakage transformer of a straight-line node maps the events `Com.ctLeak (jLeakModel Pj)`
of a program of `jasminDialect` in the stack-memory fragment `ScalarMemN` to the events of
its typed chain `straightOpsMem`. A binding `stackLoad w n` or `stackStore w n` emits the
source event `addr "" i`, `i` the value of its index; its instruction `LOADIDX`/`STOREIDX`
carries the operand `.arrIdx base idx (w/8)` and emits `addr base (w/8 * i)`. Every other
binding of the fragment lowers to an instruction with register and immediate operands,
which emits nothing; its source events (a variable-time event when `Pj` classes the
operation so) are dropped. `straightT Pj nArgs com d` is this map, a function of the
program and the source trace.

## Main definitions

* `opLeakF`, `instrLeakB`, `instrLeakF` — the events of an operand and of an instruction.
* `lsemFuelMemFLeak` — the flag machine with its leakage trace.
* `FRun`, `MemFCT` — terminating runs with their traces and constant time over them.
* `straightLeakF` — the events of a straight-line chain along `lsemStraightMem`.
* `kindLen`, `memOpB`, `addrSite`, `siteOf`, `straightT` — the leakage transformer of a
  straight-line chain.
* `AbiEntryPub`, `AbiEntryCT` — constant time on the flag machine from ABI entries whose
  valuations agree on the public labels.

## Main results

* `lsemFuelMemFLeak_fst` — the state component is `lsemFuelMemF`.
* `lsemFuelMemFLeak_det` — two terminating runs from the same state, at any fuels, agree.
* `lsemFuelMemFLeak_plain` — a plain chain from program counter `0` halts on the flag machine
  with the trace `straightLeakF` of its straight-line fold.
* `straightLeakF_straightOps` — from a state agreeing with `V`, the chain emits `straightT`
  of the source events at `V`.
* `nodeLeak_of_denote`, `nodeLeak_of_abi` — every terminating traced run of the chain from an
  agreeing entry state, or from an ABI entry, emits `straightT` of the source events.
* `straight_abiEntryCT` — a straight-line program constant time at the source has a chain
  constant time on the flag machine from ABI entries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
  (fstepF evalInstrPMemF_isLopn)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak ConstantTimeRel)

/-! ## 1. The events of an instruction -/

/-- The value of the index register `x` as a natural number: the stored value `readReg`
    reads, at its stored width. -/
def idxVal (r : LstateN) (x : String) : Nat := (r.lvm x).2.toNat

/-- The address event of an array operand. -/
def opLeakF (r : LstateN) : LOperand → List CTLeak
  | .arr b i => [.addr b (Int.ofNat i)]
  | .arrIdx b x sc => [.addr b (Int.ofNat (sc * idxVal r x))]
  | _ => []

/-- The events of an instruction that reads no flag: the address events of the operands of
    an `Lopn`, the branch event of a register conditional. -/
def instrLeakB (r : LstateN) (i : LinstrRM) : List CTLeak :=
  match i.fst with
  | .Lopn ds _ ss => (ds ++ ss).flatMap (opLeakF r)
  | .Lcond c _ => [.branch (condNZ { reg := r } c)]
  | _ => []

/-- The events of an instruction on the flag machine: the branch event of the decision a
    flag-reading conditional takes (`zf` equal to the polarity), otherwise `instrLeakB`. -/
def instrLeakF (i : LinstrRM) (s : LstateMF) : List CTLeak :=
  match flagCondCC? i with
  | some (pol, _) => [.branch (s.zf == pol)]
  | none => instrLeakB s.prog.base.reg i

/-- `condNZ` reads only the register file. -/
theorem condNZ_reg (b : LstateM) (c : LOperand) : condNZ b c = condNZ { reg := b.reg } c := rfl

/-! ## 2. The flag machine with its trace -/

/-- **The flag machine with its leakage trace**: the recursion of `lsemFuelMemF`, each step
    prepending the events `instrLeakF` of the fetched instruction at the state it runs
    from. -/
def lsemFuelMemFLeak (P : LprogM) : Nat → LstateMF → Option (LstateMF × List CTLeak)
  | 0, s => match findInstrMem P s.prog with
            | none => some (s, [])
            | some _ => none
  | fuel + 1, s =>
      match findInstrMem P s.prog with
      | none => some (s, [])
      | some i =>
          match evalInstrPMemF P i s with
          | some s' => (lsemFuelMemFLeak P fuel s').map fun r => (r.1, instrLeakF i s ++ r.2)
          | none => none

/-- The state component of the traced run is `lsemFuelMemF`. -/
theorem lsemFuelMemFLeak_fst (P : LprogM) :
    ∀ (fuel : Nat) (s : LstateMF),
      (lsemFuelMemFLeak P fuel s).map Prod.fst = lsemFuelMemF P fuel s := by
  intro fuel
  induction fuel with
  | zero =>
      intro s
      simp only [lsemFuelMemFLeak, lsemFuelMemF]
      cases findInstrMem P s.prog <;> rfl
  | succ n ih =>
      intro s
      simp only [lsemFuelMemFLeak, lsemFuelMemF]
      cases findInstrMem P s.prog with
      | none => rfl
      | some i =>
          simp only []
          cases evalInstrPMemF P i s with
          | none => rfl
          | some s' =>
              simp only []
              rw [← ih s', Option.map_map]
              rfl

/-- A halted state emits nothing. -/
theorem lsemFuelMemFLeak_halt (P : LprogM) (fuel : Nat) (s : LstateMF)
    (h : findInstrMem P s.prog = none) : lsemFuelMemFLeak P fuel s = some (s, []) := by
  cases fuel <;> simp [lsemFuelMemFLeak, h]

/-- One fetched-and-evaluated step of the traced run. -/
theorem lsemFuelMemFLeak_step (P : LprogM) (fuel : Nat) (i : LinstrRM) (s s' : LstateMF)
    (hfetch : findInstrMem P s.prog = some i) (heval : evalInstrPMemF P i s = some s') :
    lsemFuelMemFLeak P (fuel + 1) s
      = (lsemFuelMemFLeak P fuel s').map fun r => (r.1, instrLeakF i s ++ r.2) := by
  rw [lsemFuelMemFLeak, hfetch]
  simp only [heval]

/-- **Determinism of the traced run**: two terminating runs from the same state, at any
    fuels, end in the same state with the same trace. -/
theorem lsemFuelMemFLeak_det (P : LprogM) :
    ∀ (f₁ f₂ : Nat) (s : LstateMF) (r₁ r₂ : LstateMF × List CTLeak),
      lsemFuelMemFLeak P f₁ s = some r₁ → lsemFuelMemFLeak P f₂ s = some r₂ → r₁ = r₂ := by
  intro f₁
  induction f₁ with
  | zero =>
      intro f₂ s r₁ r₂ h₁ h₂
      cases hf : findInstrMem P s.prog with
      | some i => simp [lsemFuelMemFLeak, hf] at h₁
      | none =>
          rw [lsemFuelMemFLeak_halt P _ s hf] at h₁ h₂
          exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
  | succ n ih =>
      intro f₂ s r₁ r₂ h₁ h₂
      cases hf : findInstrMem P s.prog with
      | none =>
          rw [lsemFuelMemFLeak_halt P _ s hf] at h₁ h₂
          exact (Option.some.inj h₁).symm.trans (Option.some.inj h₂)
      | some i =>
          cases f₂ with
          | zero => simp [lsemFuelMemFLeak, hf] at h₂
          | succ m =>
              cases he : evalInstrPMemF P i s with
              | none => simp [lsemFuelMemFLeak, hf, he] at h₁
              | some s' =>
                  rw [lsemFuelMemFLeak_step P _ i s s' hf he] at h₁ h₂
                  obtain ⟨q₁, hq₁, rfl⟩ := Option.map_eq_some_iff.mp h₁
                  obtain ⟨q₂, hq₂, rfl⟩ := Option.map_eq_some_iff.mp h₂
                  rw [ih m s' q₁ q₂ hq₁ hq₂]

/-! ## 3. Constant time on the flag machine -/

/-- A terminating run of `P` from `s` with trace `ℓ`. -/
def FRun (P : LprogM) (s : LstateMF) (ℓ : List CTLeak) : Prop :=
  ∃ fuel t, lsemFuelMemFLeak P fuel s = some (t, ℓ)

/-- **Constant time on the flag machine**: two terminating runs of `P` from states related
    by `pubEq` have equal traces. -/
def MemFCT (P : LprogM) (pubEq : LstateMF → LstateMF → Prop) : Prop :=
  ConstantTimeRel pubEq (FRun P)

/-- A terminating run has a unique trace. -/
theorem fRun_unique {P : LprogM} {s : LstateMF} {ℓ₁ ℓ₂ : List CTLeak}
    (h₁ : FRun P s ℓ₁) (h₂ : FRun P s ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨f₁, t₁, h₁⟩ := h₁
  obtain ⟨f₂, t₂, h₂⟩ := h₂
  exact congrArg Prod.snd (lsemFuelMemFLeak_det P f₁ f₂ s _ _ h₁ h₂)

/-! ## 4. Straight-line chains -/

/-- The events of a straight-line chain along `lsemStraightMem` from `s`; a failing step
    emits the events of its instruction and stops. -/
def straightLeakF : List LinstrRM → LstateM → List CTLeak
  | [], _ => []
  | i :: is, s =>
      instrLeakB s.reg i ++
        match lsemStepMem i s with
        | some s' => straightLeakF is s'
        | none => []

theorem straightLeakF_cons_of_step {i : LinstrRM} {is : List LinstrRM} {s s' : LstateM}
    (h : lsemStepMem i s = some s') :
    straightLeakF (i :: is) s = instrLeakB s.reg i ++ straightLeakF is s' := by
  simp [straightLeakF, h]

/-- An `Lopn` that is no flag conditional emits `instrLeakB` on the flag machine. -/
theorem instrLeakF_of_lopn {i : LinstrRM} (hi : IsLopn i) (s : LstateMF) :
    instrLeakF i s = instrLeakB s.prog.base.reg i := by
  obtain ⟨d, o, src, hd⟩ := hi
  have hf : flagCondCC? i = none := by unfold flagCondCC?; rw [hd]
  simp [instrLeakF, hf]

/-- **A plain segment on the traced flag machine.** A plain chain at positions
    `lpc .. lpc + |seg| - 1` of `P`, which the straight-line fold runs from `b0` to `b`, runs
    on the traced flag machine from `b0` with any carry and overflow flags, emits
    `straightLeakF seg b0`, and continues with `f` fuel from `b` up to the carry and overflow
    flags. -/
theorem lsemFuelMemFLeak_seg (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b0 b : LstateM) (c0 o0 : Bool) (zf : Bool) (f : Nat),
      PlainLopnBody seg →
      (∀ k, k < seg.length → P.body[b0.lpc + k]? = seg[k]?) →
      lsemStraightMem seg b0 = some b →
      ∃ c o, lsemFuelMemFLeak P (seg.length + f)
          { prog := { base := { b0 with cf := c0, of := o0 }, lfn := fn }, zf := zf }
        = (lsemFuelMemFLeak P f
            { prog := { base := { b with cf := c, of := o }, lfn := fn }, zf := zf }).map
            fun r => (r.1, straightLeakF seg b0 ++ r.2) := by
  intro seg
  induction seg with
  | nil =>
      intro b0 b c0 o0 zf f _ _ hrun
      simp only [lsemStraightMem_nil, Option.some.injEq] at hrun
      subst hrun
      refine ⟨c0, o0, ?_⟩
      simp only [List.length_nil, Nat.zero_add, straightLeakF, List.nil_append]
      cases lsemFuelMemFLeak P f _ <;> rfl
  | cons i is ih =>
      intro b0 b c0 o0 zf f hplain hpos hrun
      obtain ⟨hi, hc, hm⟩ := hplain i (by simp)
      have his : PlainLopnBody is := fun j hj => hplain j (by simp [hj])
      rw [lsemStraightMem_cons] at hrun
      cases hstep : lsemStepMem i b0 with
      | none => rw [hstep] at hrun; exact absurd hrun (by simp)
      | some s1 =>
          rw [hstep] at hrun
          simp only [] at hrun
          have h1 : lsemStepMem i { b0 with cf := c0, of := o0 }
              = some { s1 with cf := c0, of := o0 } := by
            rw [lsemStepMem_setFlags, hstep]; rfl
          obtain ⟨c1, o1, hw⟩ := withALUFlags_eq i { b0 with cf := c0, of := o0 }
            { s1 with cf := c0, of := o0 }
          have hs1 : ({ { s1 with cf := c0, of := o0 } with cf := c1, of := o1 } : LstateM)
              = { s1 with cf := c1, of := o1 } := rfl
          have hfetch : findInstrMem P
              ({ prog := { base := { b0 with cf := c0, of := o0 }, lfn := fn }, zf := zf } :
                LstateMF).prog = some i := by
            show findInstrMem P { base := { b0 with cf := c0, of := o0 }, lfn := fn } = some i
            unfold findInstrMem
            rw [if_pos (show ({ base := { b0 with cf := c0, of := o0 }, lfn := fn } :
              LstatePM).lfn = P.lfn from hfn)]
            have := hpos 0 (by simp)
            simp only [Nat.add_zero, List.getElem?_cons_zero] at this
            exact this
          have heval : evalInstrPMemF P i
              { prog := { base := { b0 with cf := c0, of := o0 }, lfn := fn }, zf := zf }
              = some ⟨⟨{ s1 with cf := c1, of := o1 }, fn⟩, zf⟩ := by
            rw [evalInstrPMemF_isLopn P i _ hi]
            simp only [fstepF, hc, hm]
            rw [stepMemF_of_lsemStepMem h1, hw, hs1]
            rfl
          have hlpc : s1.lpc = b0.lpc + 1 := by
            have := stepMemF_lpc_succ i b0 _ (stepMemF_of_lsemStepMem hstep)
            simpa [withALUFlags_eq, LstateM.lpc] using this
          have hpos' : ∀ k, k < is.length → P.body[s1.lpc + k]? = is[k]? := by
            intro k hk
            have hp := hpos (k + 1) (by simpa using Nat.succ_lt_succ hk)
            rw [hlpc, show b0.lpc + 1 + k = b0.lpc + (k + 1) from by omega, hp]
            simp
          obtain ⟨c, o, hr⟩ := ih s1 b c1 o1 zf f his hpos' hrun
          refine ⟨c, o, ?_⟩
          rw [List.length_cons, show is.length + 1 + f = (is.length + f) + 1 from by omega,
            lsemFuelMemFLeak_step P _ i _ _ hfetch heval, hr, Option.map_map,
            straightLeakF_cons_of_step hstep, instrLeakF_of_lopn hi]
          simp only [Function.comp_def, List.append_assoc]

/-- **A plain chain halts on the traced flag machine with the trace of its fold.** A plain
    chain that the straight-line fold runs from `b0` (program counter `0`) to `b` halts in
    its singleton program, with fuel its length, in the state with base `b` up to the carry
    and overflow flags, with trace `straightLeakF seg b0`. -/
theorem lsemFuelMemFLeak_plain (fn : String) (seg : List LinstrRM) (hplain : PlainLopnBody seg)
    (b0 b : LstateM) (zf : Bool) (hpc : b0.lpc = 0) (hrun : lsemStraightMem seg b0 = some b) :
    ∃ c o, lsemFuelMemFLeak (singletonProgM fn seg) seg.length
        { prog := { base := b0, lfn := fn }, zf := zf }
      = some ({ prog := { base := { b with cf := c, of := o }, lfn := fn }, zf := zf },
          straightLeakF seg b0) := by
  obtain ⟨c, o, h⟩ := lsemFuelMemFLeak_seg (singletonProgM fn seg) fn rfl seg b0 b b0.cf b0.of
    zf 0 hplain (fun k _ => by rw [hpc, Nat.zero_add]; rfl) hrun
  refine ⟨c, o, ?_⟩
  have hb0 : ({ b0 with cf := b0.cf, of := b0.of } : LstateM) = b0 := rfl
  rw [Nat.add_zero, hb0] at h
  rw [h]
  have hlpc : b.lpc = seg.length := by
    have := lsemStraightMem_lpc seg b0 b hrun
    omega
  rw [lsemFuelMemFLeak_halt]
  · simp
  · show (if fn = fn then seg[({ b with cf := c, of := o } : LstateM).lpc]? else none) = none
    rw [if_pos rfl]
    exact List.getElem?_eq_none (by show seg.length ≤ b.lpc; omega)

/-! ## 5. The transformer of a straight-line program -/

open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck
open CatCrypt.Crypto.SecureCompilation.Dialects.JasminComLLeak
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift (shiftLinstr)

/-- The events of a binding: the events of its expression, then those of the body at the
    extended valuation. -/
theorem comCtLeak_var (M : LeakModel jasminDialect) {Γ : Ctxt jasminDialect}
    {t s : JasminTy} (e : Expr jasminDialect Γ s) (body : Com jasminDialect (s :: Γ) t)
    (V : Ctxt.Valuation Γ) :
    Com.ctLeak M (.var e body) V = Expr.ctLeak M e V ++ Com.ctLeak M body (V.extend (e.denote V)) :=
  rfl

/-- The number of events of an event class. -/
def kindLen : LeakKind → Nat
  | .quiet => 0
  | _ => 1

/-- The events of an operation number `kindLen` of its class. -/
theorem opLeak_length {d : Dialect} [TyDenote d.Ty] [DialectSignature d] (M : LeakModel d)
    (op : d.Op) (vals : HVector (fun t => ⟦t⟧) (DialectSignature.sig op)) :
    (opLeak M op vals).length = kindLen (M.kind op) := by
  unfold opLeak kindLen
  split <;> simp_all

/-- The events of an expression number `kindLen` of the class of its operation. -/
theorem exprCtLeak_length (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) (V : Ctxt.Valuation Γ) :
    (Expr.ctLeak (jLeakModel Pj) e V).length = kindLen (jKind Pj e.op) :=
  opLeak_length _ _ _

/-- The memory operations of `jasminDialect` with a runtime index. -/
def memOpB : JasminOp → Bool
  | .stackLoad _ _ => true
  | .stackStore _ _ => true
  | _ => false

/-- An address event `addr _ k` relabelled at the array base `b` and byte offset `sc * k`;
    every other event unchanged. -/
def addrSite (b : String) (sc : Nat) : CTLeak → CTLeak
  | .addr _ k => .addr b ((sc : Int) * k)
  | e => e

/-- The relabelling of an address event at the first source operand of an instruction:
    `addrSite b sc` at an operand `.arrIdx b _ sc`, the identity otherwise. -/
def siteOf : LinstrR → CTLeak → CTLeak
  | .Lopn _ _ (.arrIdx b _ sc :: _) => addrSite b sc
  | _ => id

/-- **The leakage transformer of a straight-line chain.** At a binding of operation `op` at
    depth `d`: the `kindLen` source events of `op` are relabelled by `siteOf` at the
    instruction of the binding when `op` is a memory operation, and dropped otherwise. -/
def straightT (Pj : JLeakParams) (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Nat →
      List CTLeak → List CTLeak
  | _, _, .ret _, _, _ => []
  | _, _, .var e body, d, ℓ =>
      (if memOpB e.op then
          (ℓ.take (kindLen (jKind Pj e.op))).map
            (siteOf (opToLinstrR e.op (regName d) (exprArgs d nArgs argName (fun _ => none) e)))
        else [])
        ++ straightT Pj nArgs body (d + 1) (ℓ.drop (kindLen (jKind Pj e.op)))

/-- At a binding of an operation that is no memory operation, the transformer drops the
    events of the binding. -/
theorem straightT_quiet (Pj : JLeakParams) (nArgs d : Nat) {Γ : Ctxt jasminDialect}
    {t s : JasminTy} (e : Expr jasminDialect Γ s) (body : Com jasminDialect (s :: Γ) t)
    (V : Ctxt.Valuation Γ) (ℓ : List CTLeak) (hm : memOpB e.op = false) :
    straightT Pj nArgs (.var e body) d (Expr.ctLeak (jLeakModel Pj) e V ++ ℓ)
      = straightT Pj nArgs body (d + 1) ℓ := by
  have hl : (Expr.ctLeak (jLeakModel Pj) e V).length = kindLen (jKind Pj e.op) :=
    opLeak_length _ _ _
  simp only [straightT, hm, Bool.false_eq_true, if_false, List.nil_append]
  rw [← hl, List.drop_left]

/-- The transformer at a binding whose events `ℓ₀` number `kindLen` of its class. -/
theorem straightT_var (Pj : JLeakParams) (nArgs d : Nat) {Γ : Ctxt jasminDialect}
    {t s : JasminTy} (e : Expr jasminDialect Γ s) (body : Com jasminDialect (s :: Γ) t)
    {ℓ₀ : List CTLeak} (ℓ : List CTLeak) (hl : ℓ₀.length = kindLen (jKind Pj e.op)) :
    straightT Pj nArgs (.var e body) d (ℓ₀ ++ ℓ)
      = (if memOpB e.op then
            ℓ₀.map (siteOf (opToLinstrR e.op (regName d)
              (exprArgs d nArgs argName (fun _ => none) e)))
          else [])
        ++ straightT Pj nArgs body (d + 1) ℓ := by
  simp only [straightT]
  rw [← hl, List.take_left, List.drop_left]

/-- The resolved operands of an expression emit no event. -/
theorem exprArgs_go_leak (r : LstateN) (d nArgs : Nat) {Γ : Ctxt jasminDialect} :
    ∀ {tys : List JasminTy} (hv : HVector (fun ty => Ctxt.Var Γ ty) tys),
      ∀ o ∈ exprArgs.go d nArgs argName (fun _ => none) hv, opLeakF r o = []
  | [], _ => by simp [exprArgs.go]
  | _ :: _, .cons v rest => by
      intro o ho
      rcases List.mem_cons.mp ho with h | h
      · rw [h, resolveVar_isReg]; rfl
      · exact exprArgs_go_leak r d nArgs rest o h

/-- The value of an index register that reads `v` at width `w`. -/
theorem idxVal_of_getW {r : LstateN} {x : String} {w : Nat} {v : BitVec w}
    (h : r.getW x w = some v) : idxVal r x = v.toNat := by
  unfold LstateN.getW at h
  split at h
  · rename_i hw
    cases Option.some.inj h
    unfold idxVal
    subst hw
    rfl
  · cases h

/-- The resolved operands of an expression emit no event. -/
theorem exprArgs_leak (r : LstateN) (d nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (e : Expr jasminDialect Γ t) :
    ∀ o ∈ exprArgs d nArgs argName (fun _ => none) e, opLeakF r o = [] :=
  exprArgs_go_leak r d nArgs e.args

/-- An `Lopn` writing a register from operands that emit nothing emits nothing. -/
theorem instrLeakB_quiet (r : LstateN) (dst opn : String) (ss : List LOperand) (tag : MemTag)
    (h : ∀ o ∈ ss, opLeakF r o = []) : instrLeakB r (.Lopn [.reg dst] opn ss, tag) = [] := by
  simp only [instrLeakB, List.flatMap_eq_nil_iff, List.mem_append, List.mem_singleton]
  rintro o (rfl | ho)
  · rfl
  · exact h o ho

/-- The shift instruction of a binding emits nothing. -/
theorem instrLeakB_shift (r : LstateN) (mnem : String) (w : Nat) (dst : String)
    (ss : List LOperand) (m : Nat) (tag : MemTag) (h : ∀ o ∈ ss, opLeakF r o = []) :
    instrLeakB r (shiftLinstr mnem w dst (ss.headD (.reg "")) m, tag) = [] := by
  apply instrLeakB_quiet
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · cases ss with
    | nil => rfl
    | cons a _ => exact h a (by simp)
  · rfl

/-- **The leakage transformer of a straight-line chain.** For a program in the stack-memory
    fragment and a state agreeing with `V` at depth `d = |Γ|`, the events of the chain
    `straightOpsMem` along the straight-line fold are `straightT` of the source events of
    the program at `V`. -/
theorem straightLeakF_straightOps (Pj : JLeakParams) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarMemN com) :
    ∀ {nArgs d : Nat} {st : LstateM} {V : Ctxt.Valuation Γ},
      Γ.length = d → nArgs ≤ d → StoreAgreesM nArgs d st V →
      straightLeakF (straightOpsMem nArgs com d) st
        = straightT Pj nArgs com d (Com.ctLeak (jLeakModel Pj) com V) := by
  induction hcom with
  | ret v =>
      intro nArgs d st V _ _ _
      rfl
  | var bop heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_var (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        bop heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_var, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | load heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_load (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.stackLoad _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_load, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_var _ _ _ _ _ _ (exprCtLeak_length Pj _ V), ← ih (by simp [hlen]) (by omega) hagree']
      congr 1
      match args with
      | .cons arr (.cons idx .nil) =>
        have hidx : st.reg.getW
            (operandName (resolveVar d nArgs argName (fun _ => none) idx)) 64
            = some (idx.lookup V) := by
          have := hagree.reg idx
          rwa [evalOperandN_resolveVar] at this
        rw [exprArgs_load heq arr idx, resolveVar_isReg arr, resolveVar_isReg idx]
        simp [memOpB, opToLinstrR, instrLeakB, opLeakF, idxVal_of_getW hidx, siteOf,
          addrSite, Expr.ctLeak, opLeak, jLeakModel, jKind]
        exact Or.inl rfl
  | store heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_store (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepArr
        ((⟨JasminOp.stackStore _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_store, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_var _ _ _ _ _ _ (exprCtLeak_length Pj _ V), ← ih (by simp [hlen]) (by omega) hagree']
      congr 1
      match args with
      | .cons arr (.cons idx (.cons val .nil)) =>
        have hidx : st.reg.getW
            (operandName (resolveVar d nArgs argName (fun _ => none) idx)) 64
            = some (idx.lookup V) := by
          have := hagree.reg idx
          rwa [evalOperandN_resolveVar] at this
        rw [exprArgs_store heq arr idx val, resolveVar_isReg arr, resolveVar_isReg idx,
          resolveVar_isReg val]
        simp [memOpB, opToLinstrR, instrLeakB, opLeakF, idxVal_of_getW hidx, siteOf,
          addrSite, Expr.ctLeak, opLeak, jLeakModel, jKind]
        exact Or.inl rfl
  | const n hwn heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_const (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        n hwn heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_const, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (by simp [opLeakF])
  | sel heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_sel, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | shr hm heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_shr (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_shr, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_shift _ _ _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | shl hm heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_shl (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_shl, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_shift _ _ _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | sar hm heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_sar (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        hm heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_sar, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_shift _ _ _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | mulhi heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_mulhi (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_mulhi, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | addLo heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_addLo (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_addLo, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | addHi heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_addHi (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_addHi, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)
  | cast heq args hbody ih =>
      intro nArgs d st V hlen harg hagree
      have hstep := lsemStepMem_cast (V := V) (st := st) (nArgs := nArgs) (curDepth := d)
        heq args hagree
      have hagree' := StoreAgreesM.stepReg
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      rw [straightOpsMem_cast, straightLeakF_cons_of_step hstep, comCtLeak_var,
        straightT_quiet _ _ _ _ _ _ _ rfl, ← ih (by simp [hlen]) (by omega) hagree']
      convert List.nil_append _ using 2
      simp only [opToLinstrR]
      split <;> exact instrLeakB_quiet _ _ _ _ _ (exprArgs_leak _ _ _ _)

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagArrLoop
  (straightOpsMem_plain scalarMemN_comOpsPlain)

/-- **The leakage of a straight-line node on the flag machine.** For a program returning a
    register in the stack-memory fragment and an entry state at program counter `0` agreeing
    with `V` (`StoreAgreesM` at depth `|Γ|` over the `|Γ|` arguments), every terminating
    traced run of its chain `straightOpsMem` on the flag machine emits `straightT` of the
    source events of the program at `V`. -/
theorem nodeLeak_of_denote (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hcom : ScalarMemN com) (V : Ctxt.Valuation Γ)
    (fn : String) (b0 : LstateM) (zf : Bool) (hpc : b0.lpc = 0)
    (hagree : StoreAgreesM Γ.length Γ.length b0 V) (fuel : Nat) (t : LstateMF)
    (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ℓ = straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V) := by
  obtain ⟨b, hb, -⟩ := lsemStraightMem_straightOps hcom (w := w) rfl rfl le_rfl hagree
  obtain ⟨c, o, h⟩ := lsemFuelMemFLeak_plain fn _
    (straightOpsMem_plain _ com (scalarMemN_comOpsPlain hcom) _) b0 b zf hpc hb
  have := lsemFuelMemFLeak_det _ _ _ _ _ _ hrun h
  rw [show ℓ = _ from congrArg Prod.snd this]
  exact straightLeakF_straightOps Pj hcom rfl le_rfl hagree

/-- **Constant time of a straight-line node on the flag machine.** If the source events of a
    program in the stack-memory fragment are equal at two valuations, the terminating traced
    runs of its chain from entry states agreeing with them have equal traces. -/
theorem nodeLeak_eq_of_ctLeak_eq (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hcom : ScalarMemN com) (fn : String)
    {V₁ V₂ : Ctxt.Valuation Γ} (hV : Com.ctLeak (jLeakModel Pj) com V₁ = Com.ctLeak (jLeakModel Pj) com V₂)
    {b₁ b₂ : LstateM} {zf₁ zf₂ : Bool} (hpc₁ : b₁.lpc = 0) (hpc₂ : b₂.lpc = 0)
    (h₁ : StoreAgreesM Γ.length Γ.length b₁ V₁) (h₂ : StoreAgreesM Γ.length Γ.length b₂ V₂)
    {ℓ₁ ℓ₂ : List CTLeak}
    (r₁ : FRun (singletonProgM fn (straightOpsMem Γ.length com Γ.length))
      { prog := { base := b₁, lfn := fn }, zf := zf₁ } ℓ₁)
    (r₂ : FRun (singletonProgM fn (straightOpsMem Γ.length com Γ.length))
      { prog := { base := b₂, lfn := fn }, zf := zf₂ } ℓ₂) : ℓ₁ = ℓ₂ := by
  obtain ⟨f₁, t₁, r₁⟩ := r₁
  obtain ⟨f₂, t₂, r₂⟩ := r₂
  rw [nodeLeak_of_denote Pj com hcom V₁ fn b₁ zf₁ hpc₁ h₁ f₁ t₁ ℓ₁ r₁,
    nodeLeak_of_denote Pj com hcom V₂ fn b₂ zf₂ hpc₂ h₂ f₂ t₂ ℓ₂ r₂, hV]

/-! ## 6. From an ABI entry -/

section Abi

open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertFragment
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry
open CatCrypt.Crypto.SecureCompilation.Haxc (AbiLayout)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.CT (ConstantTime)

/-- Two ABI entries: entry machine states with the valuations a layout reads off them and
    flag-machine entry states, whose valuations agree on the positions `L` marks public. -/
def AbiEntryPub (σ : AbiLayout) {Γ : Ctxt jasminDialect} (L : Labels Γ)
    (x y : AState × Ctxt.Valuation Γ × LstateM) : Prop :=
  AbiValOf σ x.1 x.2.1 ∧ AbiEntryM σ x.1 x.2.2 ∧ AbiValOf σ y.1 y.2.1 ∧ AbiEntryM σ y.1 y.2.2
    ∧ PubEqV L x.2.1 y.2.1

/-- **Constant time of a program on the flag machine from ABI entries**: terminating traced
    runs of `P` (function `fn`, `zf` clear) from the flag-machine entries of two ABI entries
    whose valuations agree on the public labels `L` have equal traces. -/
def AbiEntryCT (P : LprogM) (fn : String) (σ : AbiLayout) {Γ : Ctxt jasminDialect}
    (L : Labels Γ) : Prop :=
  ConstantTimeRel (AbiEntryPub σ L)
    (fun x ℓ => FRun P { prog := { base := x.2.2, lfn := fn }, zf := false } ℓ)

/-- **The leakage of a straight-line node from an ABI entry.** For a program in the
    stack-memory fragment, every terminating traced run of its chain from an ABI entry of
    `sa` emits `straightT` of the source events at the valuation `σ` reads off `sa`. -/
theorem nodeLeak_of_abi (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hmem : scalarMemNB com = true) (σ : AbiLayout)
    (sa : AState) (V : Ctxt.Valuation Γ) (fn : String) (b0 : LstateM) (zf : Bool)
    (hV : AbiValOf σ sa V) (hb : AbiEntryM σ sa b0) (fuel : Nat) (t : LstateMF)
    (ℓ : List CTLeak)
    (hrun : lsemFuelMemFLeak (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) fuel
      { prog := { base := b0, lfn := fn }, zf := zf } = some (t, ℓ)) :
    ℓ = straightT Pj Γ.length com Γ.length (Com.ctLeak (jLeakModel Pj) com V) :=
  nodeLeak_of_denote Pj com (scalarMemNB_sound com hmem) V fn b0 zf hb.pc
    (storeAgreesM_of_abi hV hb) fuel t ℓ hrun

/-- **Constant time of a straight-line node transfers to the flag machine.** A program in the
    stack-memory fragment whose source events are constant time for the labels `L` has a
    chain that is constant time on the flag machine from ABI entries. -/
theorem straight_abiEntryCT (Pj : JLeakParams) {Γ : Ctxt jasminDialect} {w : Nat}
    (com : Com jasminDialect Γ (.reg w)) (hmem : scalarMemNB com = true) (σ : AbiLayout)
    (L : Labels Γ) (fn : String)
    (hct : ConstantTime (PubEqV L) (Com.ctLeak (jLeakModel Pj) com)) :
    AbiEntryCT (singletonProgM fn (straightOpsMem Γ.length com Γ.length)) fn σ L := by
  rintro ⟨sa₁, V₁, b₁⟩ ⟨sa₂, V₂, b₂⟩ ℓ₁ ℓ₂ ⟨hV₁, hb₁, hV₂, hb₂, hp⟩ r₁ r₂
  exact nodeLeak_eq_of_ctLeak_eq Pj com (scalarMemNB_sound com hmem) fn (hct V₁ V₂ hp)
    hb₁.pc hb₂.pc (storeAgreesM_of_abi hV₁ hb₁) (storeAgreesM_of_abi hV₂ hb₂) r₁ r₂

end Abi

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFLeak
