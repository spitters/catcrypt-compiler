/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemAddrRun
public import CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs
public import CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
public import CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi

@[expose] public section

set_option autoImplicit false

/-!
# The `MULX` fusion on the flag machine

The looped-body fusion `FuseMulHi.fuseMulHiBody (saveRdx := true)` keeps each low
`MUL d, [s1, s2]` and replaces a matching `MULXHI hd, [h1, s2]` by the save of `RDX` in
`R15`, the pin `MOV:64 RDX, h1`, the two-output `MULX:64 d, hd, s2` and the restore of
`RDX`. The `MULX` writes `d` again, with the low word of `h1 * s2`, and reads both sources
at width `64`; the rewrite preserves a run when, at the `MULXHI`, `d` holds that low word
and both sources have width `64`. These are facts about the source body at the position of
the `MULXHI`, not about the instruction alone, so the simulation carries an invariant
indexed by position. The invariant is the description of the state by the symbolic step
`OwnedLprogTV.symStep`, run over the source from the last control instruction; the
decided check `fuseOKL` reads the two facts off the symbolic state.

## Main results

* `expI`, `pcI`, `ExpInv`, `lsemFuelMemF_expI`: halting runs of the flag machine
  `lsemFuelMemF` under an expansion that depends on the instruction's index, with a
  per-index invariant of the source states.
* `fuseMulHiRM`, `fuseMulHiRM_eq`: the fusion on a typed body, and its form as an expansion
  by position when the body's names avoid `R15` and `R14` and the destination and multiplier
  of each multiply are neither spill slots nor `RDX`.
* `fuseOKL`, `fuseMulHiOK`: the decided side conditions, on the source body only.
* `fuseMulHi_lsemFuelMemF`, `fuseMulHi_lsemFuelMemF_pre`: the fusion of a body, and of the
  loop part of a body, preserves halting runs from program counter `0`; the final states
  agree outside `R15`.
* `lsemFuelMemF_expI_calls`, `lsemFuelMemF_fuseOKL_calls`, `fuseMulHi_lsemFuelMemF_pre_calls`:
  the same at an instruction set whose steps contain those of `x86Isa` and whose further
  steps are local calls with word results, such as `x86Isa.withProcs T`. The analysis
  restarts after each shadow instruction of a call (`isCtlB`), so a fused site never reads
  facts from before a call.
-/

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemLoop
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagGuard
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMemFlagNestJoin
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsa (Isa retWord callShadow shadowCall?
  argsRead_none CallRes retRes lpc_retRes lfn_retRes argRead argsRead)
open CatCrypt.Crypto.SecureCompilation.VIR.LprogIsaProcs (evalInstrPMemF_shadowCall)
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_lsemFuelMemF)

/-! ## 1. Expansion by index -/

section Exp

variable (e : Nat → LinstrRM → List LinstrRM)

/-- The expansion of a body whose first instruction has index `n`: instruction `i` at
    index `k` becomes `e k i`. -/
def expI : List LinstrRM → Nat → List LinstrRM
  | [], _ => []
  | i :: is, n => e n i ++ expI is (n + 1)

theorem expI_append : ∀ (xs ys : List LinstrRM) (n : Nat),
    expI e (xs ++ ys) n = expI e xs n ++ expI e ys (n + xs.length)
  | [], ys, n => by simp [expI]
  | i :: xs, ys, n => by
      rw [List.cons_append, expI, expI, expI_append xs ys (n + 1), List.append_assoc,
        List.length_cons, show n + 1 + xs.length = n + (xs.length + 1) by omega]

/-- The position in the expanded body at which the expansion of instruction `k` begins. -/
def pcI (body : List LinstrRM) (k : Nat) : Nat := (expI e (body.take k) 0).length

theorem expI_split {body : List LinstrRM} {k : Nat} {i : LinstrRM} (h : body[k]? = some i) :
    expI e body 0
      = expI e (body.take k) 0 ++ (e k i ++ expI e (body.drop (k + 1)) (k + 1)) := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp h).1
  have hsplit : body = body.take k ++ i :: body.drop (k + 1) := by
    have hi : body[k] = i := (List.getElem?_eq_some_iff.mp h).2
    rw [← hi, List.cons_getElem_drop_succ, List.take_append_drop]
  have hlen : (body.take k).length = k := by simp; omega
  conv_lhs => rw [hsplit]
  rw [expI_append, hlen, expI, Nat.zero_add]

theorem pcI_succ {body : List LinstrRM} {k : Nat} {i : LinstrRM} (h : body[k]? = some i) :
    pcI e body (k + 1) = pcI e body k + (e k i).length := by
  have hk : k < body.length := (List.getElem?_eq_some_iff.mp h).1
  have hi : body[k] = i := (List.getElem?_eq_some_iff.mp h).2
  have hlen : (body.take k).length = k := by simp; omega
  unfold pcI
  rw [List.take_add_one, List.getElem?_eq_getElem hk, hi, Option.toList_some, expI_append,
    hlen]
  simp [expI]

/-- The expansion of instruction `k` sits at `pcI k` in the expanded body. -/
theorem getElem?_expI_pcI {body : List LinstrRM} {k : Nat} {i : LinstrRM}
    (h : body[k]? = some i) {j : Nat} (hj : j < (e k i).length) :
    (expI e body 0)[pcI e body k + j]? = (e k i)[j]? := by
  rw [expI_split e h]
  unfold pcI
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

/-- Past the end of the body the mapped position is past the end of the expansion. -/
theorem getElem?_expI_pcI_none {body : List LinstrRM} {k : Nat} (h : body[k]? = none) :
    (expI e body 0)[pcI e body k]? = none := by
  have hk : body.length ≤ k := List.getElem?_eq_none_iff.mp h
  unfold pcI
  rw [List.take_of_length_le hk]
  exact List.getElem?_eq_none_iff.mpr (Nat.le_refl _)

/-- A label position moves through the expansion, when a label expands to itself and no
    other instruction expands to a label. -/
theorem findIdx?_expI (l : LLabel) : ∀ (body : List LinstrRM) (n : Nat),
    (∀ k i, body[k]? = some i →
      (JasminLsemLabeled.isLabel l i.1 = true → e (n + k) i = [i]) ∧
      (JasminLsemLabeled.isLabel l i.1 = false →
        ∀ j ∈ e (n + k) i, JasminLsemLabeled.isLabel l j.1 = false)) →
    (expI e body n).findIdx? (fun i => JasminLsemLabeled.isLabel l i.1)
      = (body.findIdx? (fun i => JasminLsemLabeled.isLabel l i.1)).map
          (fun k => (expI e (body.take k) n).length)
  | [], n, _ => rfl
  | i :: is, n, h => by
      have his := findIdx?_expI l is (n + 1) (fun k j hk => by
        have := h (k + 1) j (by simpa using hk)
        rwa [show n + (k + 1) = n + 1 + k by omega] at this)
      obtain ⟨h1, h2⟩ := h 0 i rfl
      rw [Nat.add_zero] at h1 h2
      cases hp : JasminLsemLabeled.isLabel l i.1 with
      | true =>
          rw [expI, h1 hp]
          simp [List.findIdx?_cons, hp, expI]
      | false =>
          have hnone : (e n i).findIdx? (fun i => JasminLsemLabeled.isLabel l i.1) = none := by
            rw [List.findIdx?_eq_none_iff]
            intro j hj
            simpa using h2 hp j hj
          rw [expI, List.findIdx?_append, hnone, his]
          simp only [List.findIdx?_cons, hp, Option.none_or, Option.map_map]
          cases is.findIdx? (fun i => JasminLsemLabeled.isLabel l i.1) with
          | none => rfl
          | some k =>
              simp [expI, Nat.add_comm]

end Exp

/-! ## 2. The simulation with an invariant -/

section Sim

variable (Q : LstateM → LstateM → Prop) (G : LstateM → Prop)
  (Inv : Nat → LstateM → Bool → Prop) (e : Nat → LinstrRM → List LinstrRM)

/-- A label, a zero-flag conditional or a goto. -/
def CtlI (i : LinstrRM) : Prop :=
  (∃ kd l, i.1 = LinstrR.Llabel kd l)
    ∨ (∃ c l, i.1 = LinstrR.Lcond c l ∧ flagCondCC? i ≠ none)
    ∨ (∃ tgt, i.1 = LinstrR.Lgoto tgt)

/-- The conditions of an expansion simulation of `body` with the invariant `Inv`: every
    instruction is an `Lopn` or a control instruction that expands to itself; the expansion
    of an `Lopn` is a straight segment that reaches a `Q`-related state from a `Q`-related
    state where the source step keeps `Inv`; `Inv` implies the program-counter-free
    condition `G`, which implies `Inv` after every control instruction; and `Q` and `G` do
    not read the program counter. -/
structure ExpInv (body : List LinstrRM) : Prop where
  /-- Every instruction is an `Lopn` or a control instruction that expands to itself. -/
  cls : ∀ k i, body[k]? = some i → IsLopn i ∨ (CtlI i ∧ e k i = [i])
  /-- The expansion of an `Lopn` is a straight segment that simulates its step. -/
  lopn : ∀ k i, body[k]? = some i → IsLopn i → (∀ j ∈ e k i, IsLopn j) ∧
    ∀ (s s' t : LstateM) (zf zt : Bool), Inv k s zf → Q s s' →
      fstepF i s zf = some (t, zt) →
        Inv (k + 1) t zt ∧ ∃ t', runStraightF (e k i) s' zf = some (t', zt) ∧ Q t t'
  /-- The invariant implies `G`. -/
  ginv : ∀ k s z, Inv k s z → G s
  /-- `G` does not read the program counter. -/
  gpc : ∀ s p, G s → G (s.setLpc p)
  /-- After a control instruction, `G` implies the invariant. -/
  start : ∀ k i, body[k]? = some i → CtlI i → ∀ s z, G s → Inv (k + 1) s z
  /-- `Q` does not read the program counters. -/
  qpc : ∀ a b p q, Q a b → Q (a.setLpc p) (b.setLpc q)

/-- The state relation: function names and zero flags agree, the target program counter is
    the image of the source one, the bases are `Q`-related and the source satisfies the
    invariant at its program counter. -/
structure RelI (body : List LinstrRM) (s s' : LstateMF) : Prop where
  /-- The function names agree. -/
  lfn : s'.prog.lfn = s.prog.lfn
  /-- The zero flags agree. -/
  zf : s'.zf = s.zf
  /-- The target program counter is the image of the source program counter. -/
  pc : s'.prog.base.lpc = pcI e body s.prog.base.lpc
  /-- The bases are related. -/
  base : Q s.prog.base s'.prog.base
  /-- The source satisfies the invariant. -/
  inv : Inv s.prog.base.lpc s.prog.base s.zf

variable {Q G Inv e}

theorem nextPc_eq_setLpc (s : LstateM) : s.nextPc = s.setLpc (s.lpc + 1) := rfl

theorem findLabelMem_expI {body : List LinstrRM} (h : ExpInv Q G Inv e body) (l : LLabel) :
    findLabelMem l (expI e body 0) = (findLabelMem l body).map (pcI e body) := by
  unfold findLabelMem JasminLsemLabeled.findLabel
  rw [List.findIdx?_map, List.findIdx?_map]
  refine findIdx?_expI e l body 0 (fun k i hk => ?_)
  rw [Nat.zero_add]
  rcases h.cls k i hk with ⟨d, o, s, hd⟩ | ⟨_, hself⟩
  · refine ⟨fun hp => ?_, fun _ j hj => ?_⟩
    · simp [hd, JasminLsemLabeled.isLabel] at hp
    · obtain ⟨d', o', s', hd'⟩ := (h.lopn k i hk ⟨d, o, s, hd⟩).1 j hj
      simp [hd', JasminLsemLabeled.isLabel]
  · refine ⟨fun _ => hself, fun hp j hj => ?_⟩
    rw [hself] at hj
    obtain rfl : j = i := by simpa using hj
    exact hp

theorem evalJumpMem_expI {fn : String} {body : List LinstrRM} (h : ExpInv Q G Inv e body)
    (l : LLabel) {p p' q : LstatePM} (hQ : Q p.base p'.base) (hG : G p.base)
    (hfn : p'.lfn = p.lfn) (hj : evalJumpMem (singletonProgM fn body) l p = some q) :
    ∃ q', evalJumpMem (singletonProgM fn (expI e body 0)) l p' = some q'
      ∧ Q q.base q'.base ∧ q'.lfn = q.lfn ∧ q'.base.lpc = pcI e body q.base.lpc
      ∧ ∀ z, Inv q.base.lpc q.base z := by
  unfold evalJumpMem at hj ⊢
  simp only [singletonProgM] at hj ⊢
  rw [findLabelMem_expI h l]
  cases hl : findLabelMem l body with
  | none => simp [hl] at hj
  | some pc =>
      simp only [hl, Option.map_some] at hj ⊢
      cases hj
      obtain ⟨w, hw, hlab⟩ := JasminLsemLabeled.findLabel_sound l _ pc hl
      rw [List.getElem?_map] at hw
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hw
      have hctl : CtlI i := by
        rcases h.cls pc i hi with ⟨d, o, s, hd⟩ | ⟨hc, _⟩
        · simp [hd, JasminLsemLabeled.isLabel] at hlab
        · exact hc
      have hself : e pc i = [i] := by
        rcases h.cls pc i hi with ⟨d, o, s, hd⟩ | ⟨_, hs⟩
        · simp [hd, JasminLsemLabeled.isLabel] at hlab
        · exact hs
      refine ⟨_, rfl, h.qpc _ _ _ _ hQ, hfn, ?_, fun z => ?_⟩
      · show pcI e body pc + 1 = pcI e body (pc + 1)
        rw [pcI_succ e hi, hself]; rfl
      · exact h.start pc i hi hctl _ z (h.gpc _ _ hG)

/-- **One source step.** A successful source step at instruction `i` is matched by
    `(e k i).length` target steps of an instruction set `I` from a related state into a
    related state, when the step of `I` at every instruction of the expansion is the step of
    `x86Isa`. -/
theorem evalInstrPMemF_expI {I : Isa} {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body)
    {s s' u : LstateMF} {i : LinstrRM} (hR : RelI Q Inv e body s s')
    (hfn : s.prog.lfn = fn) (hget : body[s.prog.base.lpc]? = some i)
    (hag : ∀ j ∈ e s.prog.base.lpc i, ∀ (P : LprogM) (x : LstateMF),
      I.step P j x = x86Isa.step P j x)
    (he : evalInstrPMemF (singletonProgM fn body) i s = some u) :
    ∃ u', (∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0))
        ((e s.prog.base.lpc i).length + f) s'
          = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u')
      ∧ RelI Q Inv e body u u' := by
  set k := s.prog.base.lpc with hk
  have hfn' : s'.prog.lfn = fn := hR.lfn.trans hfn
  have hpos : ∀ j, j < (e k i).length →
      (expI e body 0)[s'.prog.base.lpc + j]? = (e k i)[j]? := by
    intro j hj
    rw [hR.pc]
    exact getElem?_expI_pcI e hget hj
  have hG : G s.prog.base := h.ginv _ _ _ hR.inv
  rcases h.cls k i hget with hlopn | ⟨hctl, hself⟩
  · obtain ⟨hex, hstep⟩ := h.lopn k i hget hlopn
    rw [evalInstrPMemF_isLopn _ i s hlopn] at he
    obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp he
    obtain ⟨b, z⟩ := bz
    obtain ⟨hinv, b', hb', hQb⟩ := hstep _ _ _ _ _ hR.inv hR.base hb
    refine ⟨{ prog := { base := b', lfn := s'.prog.lfn }, zf := z }, fun f => ?_, ?_⟩
    · have hseg := lsemFuelMemF_segF_agree (I := I) (singletonProgM fn (expI e body 0))
        s'.prog.lfn hfn' (e k i) s'.prog.base s'.zf f hex hag hpos
      rw [← hR.zf] at hb'
      rw [hb'] at hseg
      exact hseg
    · have h1 := runStraightF_lpc _ _ _ _ _ hb'
      have h2 := fstepF_lpc_succ _ _ _ _ _ hb
      refine ⟨hR.lfn, rfl, ?_, hQb, ?_⟩
      · show b'.lpc = pcI e body b.lpc
        rw [h1, h2, pcI_succ e hget, hR.pc]
      · show Inv b.lpc b z
        rw [h2]; exact hinv
  · have hfetch : findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = some i := by
      unfold findInstrMem
      rw [if_pos (show s'.prog.lfn = (singletonProgM fn (expI e body 0)).lfn from hfn')]
      have := hpos 0 (by rw [hself]; simp)
      simpa [hself, singletonProgM] using this
    have hone : ∀ {u' : LstateMF},
        evalInstrPMemF (singletonProgM fn (expI e body 0)) i s' = some u' →
        ∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0)) ((e k i).length + f) s'
          = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u' := by
      intro u' hu' f
      have hI : I.step (singletonProgM fn (expI e body 0)) i s' = some u' := by
        rw [hag i (by rw [hself]; exact List.mem_singleton_self i)]
        exact hu'
      rw [hself, List.length_singleton, Nat.add_comm]
      exact I.lsemFuelMemF_step _ f i s' u' hfetch hI
    have hnext : pcI e body (k + 1) = s'.prog.base.lpc + 1 := by
      rw [pcI_succ e hget, hself, hR.pc]; rfl
    have hinvN : ∀ z, Inv (k + 1) s.prog.base.nextPc z := fun z =>
      h.start k i hget hctl _ z (h.gpc _ _ hG)
    have hQN : Q s.prog.base.nextPc s'.prog.base.nextPc := h.qpc _ _ _ _ hR.base
    obtain ⟨wire, tag⟩ := i
    rcases hctl with ⟨kd, l, hw⟩ | ⟨c, l, hw, hcc⟩ | ⟨tgt, hw⟩
    · obtain rfl : wire = LinstrR.Llabel kd l := hw
      rw [evalInstrPMemF_label] at he
      cases he
      exact ⟨_, hone (evalInstrPMemF_label _ kd l tag s'),
        ⟨hR.lfn, hR.zf, hnext.symm, hQN, hinvN _⟩⟩
    · obtain rfl : wire = LinstrR.Lcond c l := hw
      have h1 : cmpArgs? (LinstrR.Lcond c l, tag) = none := rfl
      have h2 : movRegArgs? (LinstrR.Lcond c l, tag) = none := rfl
      cases h3 : flagCondCC? (LinstrR.Lcond c l, tag) with
      | none => exact absurd h3 hcc
      | some pl =>
          obtain ⟨pol, lbl⟩ := pl
          unfold evalInstrPMemF at he
          simp only [h1, h2, h3] at he
          split at he
          · rename_i hz
            obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
            obtain ⟨q', hq', hQq, hfq, hpq, hiq⟩ := evalJumpMem_expI h lbl hR.base hG hR.lfn hq
            refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [if_pos (hR.zf.trans hz), hq']; rfl
          · rename_i hz
            cases he
            refine ⟨{ s' with prog := { s'.prog with base := s'.prog.base.nextPc } },
              hone ?_, ⟨hR.lfn, hR.zf, hnext.symm, hQN, hinvN _⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [if_neg (fun h => hz (hR.zf.symm.trans h))]
    · obtain rfl : wire = LinstrR.Lgoto tgt := hw
      obtain ⟨gfn, l⟩ := tgt
      have hev : ∀ (R : LprogM) (x : LstateMF),
          evalInstrPMemF R (LinstrR.Lgoto (gfn, l), tag) x
            = (if gfn = R.lfn then evalJumpMem R l x.prog else none).map
                (fun p => { x with prog := p }) := fun R x => by
        rw [evalInstrPMemF_delegate R _ x rfl rfl rfl rfl rfl rfl]; rfl
      rw [hev] at he
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp he
      split at hq
      · rename_i hf
        obtain ⟨q', hq', hQq, hfq, hpq, hiq⟩ := evalJumpMem_expI h l hR.base hG hR.lfn hq
        refine ⟨{ s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
        rw [hev, if_pos (show gfn = (singletonProgM fn (expI e body 0)).lfn from hf), hq']; rfl
      · exact absurd hq (by simp)

/-- **One step of a shadow instruction of a call.** At an instruction set `I` whose steps
    beyond `x86Isa` are local calls at the array positions `aa`, a step of the call at
    instruction `i`, which expands to itself, is matched by the same call from a related
    state, when the relation and the invariant give equal argument words and are kept by the
    write of every result, a word or a word array. -/
theorem step_expI_call {I : Isa} {aa : String → Nat → Option Nat} {ao : String → Option Nat}
    (hcl : I.CallLocal x86Isa aa ao)
    {fn : String} {body : List LinstrRM} {s s' u : LstateMF} {i : LinstrRM}
    (hR : RelI Q Inv e body s s') (hfn : s.prog.lfn = fn)
    (hget : body[s.prog.base.lpc]? = some i) (hsh : shadowCall? i.1 ≠ none)
    (hself : e s.prog.base.lpc i = [i])
    (hfacts : ∀ (dst f : String) (srcs : List LOperand), i.1 = callShadow dst f srcs →
      ∀ (x : CallRes),
        argsRead (aa f) s'.prog.base 0 srcs = argsRead (aa f) s.prog.base 0 srcs
          ∧ Inv (s.prog.base.lpc + 1) (retRes dst x s).prog.base s.zf
          ∧ Q (retRes dst x s).prog.base (retRes dst x s').prog.base)
    (he : I.step (singletonProgM fn body) i s = some u) :
    ∃ u', (∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0))
        ((e s.prog.base.lpc i).length + f) s'
          = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u')
      ∧ RelI Q Inv e body u u' := by
  rcases hcl _ i s u he with hx | ⟨dst, f, srcs, x, hi, rfl, hfwd, -⟩
  · have hx' : evalInstrPMemF (singletonProgM fn body) i s = some u := hx
    rw [evalInstrPMemF_shadowCall _ i s hsh] at hx'
    cases hx'
  · obtain ⟨hargs, hinv, hQ⟩ := hfacts dst f srcs hi x
    have hfetch : findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = some i := by
      rw [findInstrMem_singleton fn _ s'.prog (hR.lfn.trans hfn), hR.pc]
      have := getElem?_expI_pcI e hget (j := 0) (by rw [hself]; simp)
      rw [Nat.add_zero, hself] at this
      simpa using this
    obtain ⟨w, tag⟩ := i
    simp only at hi
    subst hi
    have hstep : I.step (singletonProgM fn (expI e body 0)) (callShadow dst f srcs, tag) s'
        = some (retRes dst x s') :=
      hfwd _ tag dst srcs s' rfl hargs
    have hz : ∀ y : LstateMF, (retRes dst x y).zf = y.zf := fun y => by cases x <;> rfl
    refine ⟨retRes dst x s', fun f' => ?_, ⟨by rw [lfn_retRes, lfn_retRes]; exact hR.lfn,
      by rw [hz, hz]; exact hR.zf, ?_, hQ, ?_⟩⟩
    · rw [hself, List.length_singleton, Nat.add_comm]
      exact I.lsemFuelMemF_step _ f' _ s' _ hfetch hstep
    · rw [lpc_retRes, lpc_retRes, pcI_succ e hget, hself, hR.pc]
      rfl
    · rw [lpc_retRes, hz]
      exact hinv

/-- **An index-dependent expansion with an invariant at an instruction set with local
    calls.** Let `I` be an instruction set whose steps contain those of `x86Isa` and whose
    further steps are local calls at the array positions `aa`. When the step of `I` at every
    instruction of the expansion of an instruction that is no shadow instruction of a call is
    the step of `x86Isa`, and each shadow instruction of a call that `I` steps expands to
    itself with equal argument words on related states and with the relation and the
    invariant kept by the write of every result, every halting run of `I` on the source body
    is matched, from a related state, by a halting run of `I` on the expanded body into a
    related state, with fuel at most `fuel * m` for a bound `m` on the expansion lengths. -/
theorem lsemFuelMemF_expI_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body)
    (hag : ∀ k i, body[k]? = some i → shadowCall? i.1 = none →
      ∀ j ∈ e k i, ∀ (P : LprogM) (x : LstateMF), I.step P j x = x86Isa.step P j x)
    (hcall : ∀ k i, body[k]? = some i → shadowCall? i.1 ≠ none →
      (∃ (P : LprogM) (x u : LstateMF), I.step P i x = some u) →
      e k i = [i] ∧ ∀ (dst f : String) (srcs : List LOperand), i.1 = callShadow dst f srcs →
        ∀ (s s' : LstateMF) (x : CallRes), Inv k s.prog.base s.zf → Q s.prog.base s'.prog.base →
          argsRead (aa f) s'.prog.base 0 srcs = argsRead (aa f) s.prog.base 0 srcs
            ∧ Inv (k + 1) (retRes dst x s).prog.base s.zf
            ∧ Q (retRes dst x s).prog.base (retRes dst x s').prog.base)
    {m : Nat} (hm : ∀ k i, body[k]? = some i → (e k i).length ≤ m) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelI Q Inv e body s s' →
      I.lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel * m
        ∧ I.lsemFuelMemF (singletonProgM fn (expI e body 0)) fuel' s' = some t'
        ∧ RelI Q Inv e body t t' := by
  have hhalt : ∀ {s s' : LstateMF}, RelI Q Inv e body s s' →
      findInstrMem (singletonProgM fn body) s.prog = none →
      findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = none := by
    intro s s' hR hf
    unfold findInstrMem at hf ⊢
    rw [hR.lfn]
    split
    · rename_i hfn
      rw [if_pos (show s.prog.lfn = (singletonProgM fn body).lfn from hfn)] at hf
      rw [hR.pc]
      exact getElem?_expI_pcI_none e (body := body) hf
    · rfl
  intro fuel
  induction fuel with
  | zero =>
      intro s s' t hR hrun
      unfold Isa.lsemFuelMemF at hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          simp only [hf] at hrun
          cases hrun
          exact ⟨0, s', by simp, I.lsemFuelMemF_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i => simp [hf] at hrun
  | succ n ih =>
      intro s s' t hR hrun
      unfold Isa.lsemFuelMemF at hrun
      cases hf : findInstrMem (singletonProgM fn body) s.prog with
      | none =>
          simp only [hf] at hrun
          cases hrun
          exact ⟨0, s', by simp, I.lsemFuelMemF_halt _ 0 s' (hhalt hR hf), hR⟩
      | some i =>
          simp only [hf] at hrun
          have hfg : s.prog.lfn = fn ∧ body[s.prog.base.lpc]? = some i := by
            unfold findInstrMem at hf
            split at hf
            · exact ⟨by assumption, hf⟩
            · simp at hf
          cases he : I.step (singletonProgM fn body) i s with
          | none => simp [he] at hrun
          | some u =>
              simp only [he] at hrun
              have hstep : ∃ u', (∀ f, I.lsemFuelMemF (singletonProgM fn (expI e body 0))
                  ((e s.prog.base.lpc i).length + f) s'
                    = I.lsemFuelMemF (singletonProgM fn (expI e body 0)) f u')
                  ∧ RelI Q Inv e body u u' := by
                by_cases hsh : shadowCall? i.1 = none
                · have he' : evalInstrPMemF (singletonProgM fn body) i s = some u := by
                    rw [← he]
                    exact (Isa.CallLocal.step_eq I hle hcl _ hsh s).symm
                  exact evalInstrPMemF_expI h hR hfg.1 hfg.2 (hag _ i hfg.2 hsh) he'
                · obtain ⟨hself, hfacts⟩ := hcall _ i hfg.2 hsh ⟨_, _, _, he⟩
                  exact step_expI_call hcl hR hfg.1 hfg.2 hsh hself
                    (fun dst f srcs hi x => hfacts dst f srcs hi s s' x hR.inv hR.base) he
              obtain ⟨u', hrun1, hRu⟩ := hstep
              obtain ⟨f', t', hf', hrun', hRt⟩ := ih hRu hrun
              have hlen := hm _ i hfg.2
              refine ⟨(e s.prog.base.lpc i).length + f', t', ?_, by rw [hrun1]; exact hrun',
                hRt⟩
              rw [Nat.succ_mul]
              omega

/-- **The flag machine under an index-dependent expansion with an invariant.** Every
    halting run of the source body is matched, from a related state, by a halting run of
    the expanded body into a related state, with fuel at most `fuel * m` for a bound `m` on
    the expansion lengths. -/
theorem lsemFuelMemF_expI {fn : String} {body : List LinstrRM} (h : ExpInv Q G Inv e body)
    {m : Nat} (hm : ∀ k i, body[k]? = some i → (e k i).length ≤ m) :
    ∀ (fuel : Nat) {s s' t : LstateMF}, RelI Q Inv e body s s' →
      lsemFuelMemF (singletonProgM fn body) fuel s = some t →
      ∃ fuel' t', fuel' ≤ fuel * m
        ∧ lsemFuelMemF (singletonProgM fn (expI e body 0)) fuel' s' = some t'
        ∧ RelI Q Inv e body t t' := by
  rw [← x86Isa_lsemFuelMemF]
  refine lsemFuelMemF_expI_calls (Isa.StepLe.refl x86Isa)
    (Isa.CallLocal.refl x86Isa (fun _ _ => none)) h (fun _ _ _ _ _ _ _ _ => rfl)
    (fun _ i _ hsh ⟨P, x, u, hu⟩ => ?_) hm
  have hu' : evalInstrPMemF P i x = some u := hu
  rw [evalInstrPMemF_shadowCall P i x hsh] at hu'
  cases hu'

end Sim

/-! ## 3. The fusion as an expansion by index -/

section Fuse

open CatCrypt.Crypto.SecureCompilation.X86Backend.FuseMulHi
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames)

/-- A name the fusion leaves alone: not a reload scratch. -/
def nameOK (n : String) : Bool :=
  n != "R15" && n != "R14"

/-- A low `MUL` or a `MULXHI` has a destination and a multiplier that are neither spill slots,
    the operands the fusion reloads through a scratch when they are spilled, nor `RDX`, the
    register the fused site pins; every other instruction passes. -/
def mulOK : LinstrR → Bool
  | .Lopn [.reg d] opn [.reg _, .reg s2] =>
      !(isLowMulMnem opn || isMulHiMnem opn)
        || (!(LOperand.reg d).isSpill && !(LOperand.reg s2).isSpill
          && d != "RDX" && s2 != "RDX")
  | _ => true

/-- The names of the wire are left alone by the fusion, the operands of a multiply are no
    spill slots, and its mnemonic is not the untagged `MULX`. -/
def wireOK (i : LinstrR) : Bool :=
  ((instrNames i).all nameOK && mulOK i) && (match i with | .Lopn _ o _ => o != "MULX" | _ => true)

theorem mulOK_spill {d opn s1 s2 : String}
    (h : mulOK (.Lopn [.reg d] opn [.reg s1, .reg s2]) = true)
    (hm : (isLowMulMnem opn || isMulHiMnem opn) = true) :
    (LOperand.reg d).isSpill = false ∧ (LOperand.reg s2).isSpill = false
      ∧ d ≠ "RDX" ∧ s2 ≠ "RDX" := by
  simp only [mulOK, hm, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
    bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- The low destination of each fused `MULXHI`, by position: the pending-`MUL` matching of
    `fuseMulHiAux` with the identity scratch environment. -/
def fuseLoAux : List (String × String) → List LinstrR → List (Option String)
  | _, [] => []
  | pend, i :: rest =>
    match i with
    | .Lopn [.reg d] opn [.reg _, .reg s2] =>
        if isLowMulMnem opn then none :: fuseLoAux ((d, s2) :: pend) rest
        else if isMulHiMnem opn then
          match pend.span (fun p => p.2 != s2) with
          | (before, (loDst, _) :: after) => some loDst :: fuseLoAux (before ++ after) rest
          | (_, []) => none :: fuseLoAux pend rest
        else none :: fuseLoAux pend rest
    | _ => none :: fuseLoAux pend rest

/-- The fused sequence of a `MULXHI` with low destination `d`, on `Linstr`. -/
def siteL (d : String) (i : Linstr) : Lcmd :=
  match i.li_i with
  | .Lopn [.reg hd] _ [.reg h1, .reg s2] =>
      [⟨i.li_ii, .Lopn [.reg "R15"] "MOVQ" [.reg "RDX"]⟩,
       ⟨i.li_ii, .Lopn [.reg "RDX"] "MOV:64" [.reg h1]⟩,
       ⟨i.li_ii, .Lopn [.reg d, .reg hd] "MULX" [.reg s2]⟩,
       ⟨i.li_ii, .Lopn [.reg "RDX"] "MOVQ" [.reg "R15"]⟩]
  | _ => [i]

/-- A body with each position expanded by its low destination. -/
def fuseL : Lcmd → List (Option String) → Lcmd
  | i :: is, lo :: los =>
      (match lo with | some d => siteL d i | none => [i]) ++ fuseL is los
  | _, _ => []

theorem scratchStep_nil {i : Linstr} (h : wireOK i.li_i = true) : scratchStep [] i = [] := by
  unfold scratchStep
  split
  · rename_i dsts opn srcs hi
    have hd : ∀ dn, LOperand.reg dn ∈ dsts → fuseReloadScratches.contains dn = false := by
      intro dn hdn
      have hall := (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1
      rw [hi] at hall
      have hn := List.all_eq_true.mp hall dn (by
        simp only [instrNames, List.flatMap_append, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨_, hdn, by simp [opNames]⟩)
      simp only [nameOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
      simp [fuseReloadScratches, reloadScratch, reloadScratch2, hn.1, hn.2]
    clear hi
    induction dsts with
    | nil => rfl
    | cons d ds ih =>
        rw [List.foldl_cons]
        cases d with
        | reg dn =>
            simp only [hd dn (by simp), Bool.false_eq_true, if_false]
            exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx))
        | _ => exact ih (fun x hx => hd x (List.mem_cons_of_mem _ hx))
  · rfl

theorem scratchResolve_nil (r : String) : scratchResolve [] r = r := rfl

theorem beq_rdx {n : String} (h : n ≠ "RDX") : (n == "RDX") = false := by
  simp [h]

theorem foldl_scratchKill_nil (xs : List String) : xs.foldl scratchKill [] = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem mem_of_span {α : Type} {p : α → Bool} {l a b : List α} (h : l.span p = (a, b))
    {x : α} (hx : x ∈ a ∨ x ∈ b) : x ∈ l := by
  rw [List.span_eq_takeWhile_dropWhile] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rw [← List.takeWhile_append_dropWhile (p := p) (l := l)]
  exact List.mem_append.mpr hx

theorem nameOK_of_mem {i : LinstrR} (h : wireOK i = true) {n : String}
    (hn : n ∈ instrNames i) : nameOK n = true :=
  List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).1 n hn

theorem mulOK_of_wireOK {i : LinstrR} (h : wireOK i = true) : mulOK i = true :=
  (Bool.and_eq_true _ _ ▸ (Bool.and_eq_true _ _ ▸ h).1).2

/-- **The looped-body fusion as an expansion by position.** On a body whose names are left
    alone by the fusion, `fuseMulHiAux` keeps every instruction except a matched `MULXHI`,
    which it expands by `siteL` with the low destination `fuseLoAux` assigns. -/
theorem fuseMulHiAux_eq : ∀ (xs : Lcmd) (pend : List (String × String)),
    (∀ p ∈ pend, nameOK p.1 = true ∧ (LOperand.reg p.1).isSpill = false ∧ p.1 ≠ "RDX") →
    (∀ i ∈ xs, wireOK i.li_i = true) →
    fuseMulHiAux true [] pend xs = fuseL xs (fuseLoAux pend (xs.map (·.li_i)))
  | [], _, _, _ => by rw [fuseMulHiAux]; rfl
  | i :: rest, pend, hp, hx => by
      have hi := hx i (by simp)
      have hr : ∀ j ∈ rest, wireOK j.li_i = true := fun j hj => hx j (by simp [hj])
      rw [fuseMulHiAux]
      simp only [scratchStep_nil hi, List.map_cons]
      obtain ⟨ii, w⟩ := i
      dsimp only at hi ⊢
      simp only [fuseLoAux, scratchResolve_nil, lowHome_nil, ite_self]
      split
      · rename_i d opn s1 s2
        have hn : ∀ n ∈ [d, s1, s2], nameOK n = true := fun n hn =>
          nameOK_of_mem hi (by simp [instrNames, opNames] at hn ⊢; omega)
        have hd := hn d (by simp)
        have hm := mulOK_of_wireOK hi
        by_cases hlo : isLowMulMnem opn = true
        · have hsp := mulOK_spill hm (by simp [hlo])
          simp only [hlo, if_true, fuseL, List.singleton_append]
          rw [fuseMulHiAux_eq rest ((d, s2) :: pend)
            (fun p hp' => by
              rcases List.mem_cons.mp hp' with rfl | hp'
              · exact ⟨hd, hsp.1, hsp.2.2.1⟩
              · exact hp p hp') hr]
        · simp only [hlo, Bool.false_eq_true, if_false]
          by_cases hhi : isMulHiMnem opn = true
          · have hspm := mulOK_spill hm (by simp [hhi])
            simp only [hhi, if_true]
            rcases hsp : List.span (fun p => p.2 != s2) pend with ⟨before, _ | ⟨⟨loDst, x⟩, after⟩⟩
            · simp only [hsp, fuseL, List.singleton_append]
              rw [fuseMulHiAux_eq rest pend hp hr]
            · have hlo2 := hp (loDst, x) (mem_of_span hsp (Or.inr (by simp)))
              simp only [hsp, hspm.1, beq_rdx hspm.2.2.1, hspm.2.1, beq_rdx hspm.2.2.2,
                hlo2.2.1, foldl_scratchKill_nil, Bool.and_false,
                Bool.false_eq_true, if_false, Bool.not_false, fuseL, siteL]
              have hb : (loDst != "RDX") = true := by simp [bne, beq_rdx hlo2.2.2]
              rw [fuseMulHiAux_eq rest (before ++ after)
                (fun p hp' => hp p (mem_of_span hsp (by
                  rcases List.mem_append.mp hp' with h | h
                  · exact Or.inl h
                  · exact Or.inr (List.mem_cons_of_mem _ h)))) hr]
              simp [hb]
          · simp only [hhi, Bool.false_eq_true, if_false, fuseL, List.singleton_append]
            rw [fuseMulHiAux_eq rest pend hp hr]
      · rename_i hne
        split
        · exact (hne _ _ _ _ rfl).elim
        · simp only [fuseL, List.singleton_append]
          rw [fuseMulHiAux_eq rest pend hp hr]

theorem length_fuseLoAux : ∀ (pend : List (String × String)) (xs : List LinstrR),
    (fuseLoAux pend xs).length = xs.length
  | _, [] => rfl
  | pend, i :: rest => by
      unfold fuseLoAux
      split
      · split
        · simp [length_fuseLoAux]
        · split
          · split <;> simp [length_fuseLoAux]
          · simp [length_fuseLoAux]
      · simp [length_fuseLoAux]

/-- The widening multiply `MULX` read at its width `MULX:64`; every other instruction
    unchanged. -/
def normMulx : LinstrR → LinstrR
  | .Lopn ds o ss => .Lopn ds (if o = "MULX" then withWidthTag 64 "MULX" else o) ss
  | i => i

/-- The address-machine reading `normA` absorbs `normMulx`. -/
theorem normA_normMulx (i : LinstrR) :
    JasminLsemAddrRun.normA (normMulx i) = JasminLsemAddrRun.normA i := by
  cases i with
  | Lopn ds o ss =>
    by_cases ho : o = "MULX"
    · subst ho
      have h1 : X86Backend.LprogAsmPrinter.untagCaret (withWidthTag 64 "MULX") = "MULX:64" :=
        X86Backend.LprogAsmPrinter.untagCaret_of_caret_free (by decide +kernel)
      have h2 : X86Backend.LprogAsmPrinter.untagCaret "MULX" = "MULX" :=
        X86Backend.LprogAsmPrinter.untagCaret_of_caret_free (by decide)
      simp only [normMulx, if_true, JasminLsemAddrRun.normA, h1, h2]
      rfl
    · simp only [normMulx, ho, if_false]
  | _ => rfl

/-- The looped-body `MULX` fusion `fuseMulHiBody (saveRdx := true)` on a typed body: each
    output instruction at the tag of the input instruction it comes from, and the widening
    multiply read at its width (`normMulx`). -/
def fuseMulHiRM (c : List LinstrRM) : List LinstrRM :=
  let body : Lcmd := c.mapIdx fun k i => ⟨k, i.1⟩
  (fuseMulHiBody body true).map fun j =>
    (normMulx j.li_i, ((c[j.li_ii]?).map (·.2)).getD (.reg none))

/-- The low destination `fuseMulHiRM` assigns to each position of a typed body. -/
def fuseLo (c : List LinstrRM) : List (Option String) := fuseLoAux [] (c.map Prod.fst)

/-- The fused sequence of a typed `MULXHI hd, [h1, s2]` with low destination `d`: save
    `RDX` in `R15`, pin `h1` in `RDX`, the two-output `MULX:64 d, hd, s2`, restore `RDX`. -/
def fuseSiteExp (d : String) (i : LinstrRM) : List LinstrRM :=
  match i.1 with
  | .Lopn [.reg hd] _ [.reg h1, .reg s2] =>
      [(.Lopn [.reg "R15"] "MOVQ" [.reg "RDX"], i.2),
       (.Lopn [.reg "RDX"] "MOV:64" [.reg h1], i.2),
       (.Lopn [.reg d, .reg hd] (withWidthTag 64 "MULX") [.reg s2], i.2),
       (.Lopn [.reg "RDX"] "MOVQ" [.reg "R15"], i.2)]
  | _ => [i]

/-- The expansion of position `k` under the low-destination list `L`. -/
def fuseE (L : List (Option String)) (k : Nat) (i : LinstrRM) : List LinstrRM :=
  match L[k]? with
  | some (some d) => fuseSiteExp d i
  | _ => [i]

theorem normMulx_of_wireOK {w : LinstrR} (h : wireOK w = true) : normMulx w = w := by
  unfold normMulx
  split
  · rename_i ds o ss
    have : o ≠ "MULX" := by
      have h2 := (Bool.and_eq_true _ _ ▸ h).2
      simpa using h2
    simp [this]
  · rfl

theorem map_fuseL (c : List LinstrRM) (L : List (Option String))
    (hc : ∀ i ∈ c, wireOK i.1 = true) :
    ∀ (xs : List LinstrRM) (n : Nat), (∀ k i, xs[k]? = some i → c[n + k]? = some i) →
      n + xs.length ≤ L.length →
      (fuseL (xs.mapIdx fun k i => ⟨n + k, i.1⟩) (L.drop n)).map
          (fun j => (normMulx j.li_i, ((c[j.li_ii]?).map (·.2)).getD (.reg none)))
        = expI (fuseE L) xs n
  | [], n, _, _ => by
      cases h : L.drop n <;> simp [fuseL, expI]
  | i :: is, n, hx, hlen => by
      have hcn : c[n]? = some i := by simpa using hx 0 i rfl
      have hwi : wireOK i.1 = true := hc i (List.mem_of_getElem? hcn)
      have hn : n < L.length := by simp at hlen; omega
      rw [List.mapIdx_cons, List.drop_eq_getElem_cons hn, expI]
      have ih := map_fuseL c L hc is (n + 1)
        (fun k j hk => by
          rw [show n + 1 + k = n + (k + 1) by omega]; exact hx (k + 1) j (by simpa using hk))
        (by simp at hlen; omega)
      have hmi : (is.mapIdx fun k j => (⟨n + (k + 1), j.1⟩ : Linstr))
          = is.mapIdx fun k j => ⟨n + 1 + k, j.1⟩ := by
        congr 1; funext k j; rw [show n + (k + 1) = n + 1 + k by omega]
      simp only [Nat.add_zero, fuseL, List.map_append]
      rw [hmi, ih]
      congr 1
      unfold fuseE
      rw [List.getElem?_eq_getElem hn]
      obtain ⟨w, tag⟩ := i
      cases L[n] with
      | none => simp [hcn, normMulx_of_wireOK hwi]
      | some d =>
          simp only [siteL, fuseSiteExp]
          split
          · simp [hcn, normMulx, withWidthTag]
          · simp [hcn, normMulx_of_wireOK hwi]

/-- **The fusion is an expansion by position.** On a typed body whose names the fusion
    leaves alone, `fuseMulHiRM` keeps every instruction except each matched `MULXHI`, which
    becomes `fuseSiteExp` at the low destination `fuseLo` assigns. -/
theorem fuseMulHiRM_eq (c : List LinstrRM) (hc : ∀ i ∈ c, wireOK i.1 = true) :
    fuseMulHiRM c = expI (fuseE (fuseLo c)) c 0 := by
  have hb : ∀ i ∈ (c.mapIdx fun k i => (⟨k, i.1⟩ : Linstr)), wireOK i.li_i = true := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := List.mem_mapIdx.mp hj
    exact hc _ (List.getElem_mem hk)
  have hmap : (c.mapIdx fun k i => (⟨k, i.1⟩ : Linstr)).map (·.li_i) = c.map Prod.fst := by
    apply List.ext_getElem <;> simp
  unfold fuseMulHiRM fuseMulHiBody
  simp only []
  rw [fuseMulHiAux_eq _ [] (by simp) hb, hmap]
  have h := map_fuseL c (fuseLo c) hc c 0 (by simp) (by simp [fuseLo, length_fuseLoAux])
  simp only [Nat.zero_add, List.drop_zero] at h
  exact h

end Fuse

/-! ## 4. The steps of the fused body -/

section Steps

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportTransfer (renRM renLinstrR renOperand)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportLower (fstepF_setLpc)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

/-- The names the fused body may change beyond the source: `R15`, which holds the saved
    `RDX`. -/
def KeptN (r : String) : Prop := r ≠ "R15"

/-- Two bases agree on every register and array name other than `R15`, on the word memory
    and on the carry and overflow flags. -/
structure Agree (s s' : LstateM) : Prop where
  /-- The registers agree outside `R15`. -/
  reg : ∀ r, KeptN r → s'.reg.lvm r = s.reg.lvm r
  /-- The arrays agree outside `R15`. -/
  arr : ∀ r, KeptN r → s'.larr r = s.larr r
  /-- The word memories agree. -/
  mem : s'.lmem = s.lmem
  /-- The carry flags agree. -/
  cf : s'.cf = s.cf
  /-- The overflow flags agree. -/
  of : s'.of = s.of

theorem Agree.refl (s : LstateM) : Agree s s := ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Agree.setLpc {a b : LstateM} (h : Agree a b) (p q : Nat) :
    Agree (a.setLpc p) (b.setLpc q) := ⟨h.reg, h.arr, h.mem, h.cf, h.of⟩

theorem renOperand_id (o : LOperand) : renOperand id o = o := by cases o <;> rfl

theorem renRM_id (i : LinstrRM) : renRM id i = i := by
  obtain ⟨w, t⟩ := i
  have h : renOperand id = id := funext renOperand_id
  cases w <;> simp [renRM, renLinstrR, h]

theorem renOn_id : RenOn id KeptN := ⟨fun _ _ _ _ h => h, by simp [KeptN], rfl⟩

/-- The empty program, the frame of a single step. -/
def emptyP : LprogM := ⟨"", []⟩

theorem renProg_empty : RenProg id KeptN 0 emptyP emptyP :=
  ⟨rfl, fun _ => rfl, fun k _ => by simp [emptyP], fun k i _ h => by simp [emptyP] at h,
    fun k i _ h => by simp [emptyP] at h, fun l pc h => by simp⟩

/-- **A source instruction on agreeing bases.** An `Lopn` that does not mention `R15` and is
    not a `MULX` steps from agreeing bases to agreeing bases, with the same zero flag. -/
theorem fstepF_agree {i : LinstrRM} (hl : IsLopn i) (hn : ∀ n ∈ instrNames i.1, KeptN n)
    (hm : mulxFree i = true) {s s' t : LstateM} {zf zt : Bool} (hA : Agree s s')
    (h : fstepF i s zf = some (t, zt)) :
    ∃ t', fstepF i s' zf = some (t', zt) ∧ Agree t t' := by
  let S : LstateMF := { prog := { base := s, lfn := "" }, zf := zf }
  let S' : LstateMF := { prog := { base := s'.setLpc s.lpc, lfn := "" }, zf := zf }
  have hR : RelF id KeptN S S' :=
    ⟨⟨⟨rfl, fun r hr => hA.reg r hr⟩, fun r hr => hA.arr r hr, hA.mem⟩, rfl, rfl, hA.cf,
      hA.of⟩
  have hc : CondOK i := ⟨fun c l he => (by
    obtain ⟨d, o, s0, hd⟩ := hl; rw [hd] at he; cases he), hm⟩
  have he : evalInstrPMemF emptyP i S
      = some { prog := { base := t, lfn := "" }, zf := zt } := by
    rw [evalInstrPMemF_isLopn _ i S hl]
    show (fstepF i s zf).map _ = _
    rw [h]; rfl
  obtain ⟨T', hT', hRT, -⟩ := evalInstrPMemF_ren renOn_id renProg_empty i hn hc hR
    (Nat.zero_le _) he
  rw [renRM_id, evalInstrPMemF_isLopn _ i S' hl] at hT'
  obtain ⟨bz, hb, rfl⟩ := Option.map_eq_some_iff.mp hT'
  have hb' : fstepF i (s'.setLpc s.lpc) zf = some bz := hb
  rw [fstepF_setLpc] at hb'
  obtain ⟨⟨t'', z''⟩, h'', hbz⟩ := Option.map_eq_some_iff.mp hb'
  subst hbz
  obtain ⟨⟨⟨-, hreg⟩, harr, hmem⟩, -, hzf, hcf, hof⟩ := hRT
  refine ⟨t'', ?_, ⟨fun r hr => hreg r hr, fun r hr => harr r hr, hmem, hcf, hof⟩⟩
  rw [h'']
  simp only at hzf
  rw [hzf]

/-- A register copy steps by writing the source cell to the destination. -/
theorem fstepF_copy {i : LinstrRM} {dst src : String} (hc : cmpArgs? i = none)
    (hm : movRegArgs? i = some (dst, src)) (s : LstateM) (zf : Bool) :
    fstepF i s zf = some ((s.setReg dst (s.reg.lvm src).2).nextPc, zf) := by
  unfold fstepF
  rw [hc, hm]
  rfl

theorem fstepF_saveRdx (tag : MemTag) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg "R15"] "MOVQ" [.reg "RDX"], tag) s zf
      = some ((s.setReg "R15" (s.reg.lvm "RDX").2).nextPc, zf) :=
  fstepF_copy (by simp only [cmpArgs?])
    (by simp only [movRegArgs?]; rw [if_neg (by decide), if_pos (by decide)]) s zf

theorem fstepF_restoreRdx (tag : MemTag) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg "RDX"] "MOVQ" [.reg "R15"], tag) s zf
      = some ((s.setReg "RDX" (s.reg.lvm "R15").2).nextPc, zf) :=
  fstepF_copy (by simp only [cmpArgs?])
    (by simp only [movRegArgs?]; rw [if_neg (by decide), if_pos (by decide)]) s zf

theorem fstepF_pinRdx (h1 : String) (tag : MemTag) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg "RDX"] "MOV:64" [.reg h1], tag) s zf
      = some ((s.setReg "RDX" (s.reg.lvm h1).2).nextPc, zf) :=
  fstepF_copy (by simp only [cmpArgs?])
    (by simp only [movRegArgs?]; rw [if_pos (by decide)]) s zf

theorem fstepF_mulx64 (d hd s2 : String) (tag : MemTag) (s : LstateM) (zf : Bool) :
    fstepF (.Lopn [.reg d, .reg hd] (withWidthTag 64 "MULX") [.reg s2], tag) s zf
      = (wideStep (.mulx d hd (.reg s2)) s).map (fun t => (t, zf)) := by
  have hw : wideArgs? ((.Lopn [.reg d, .reg hd] (withWidthTag 64 "MULX") [.reg s2] : LinstrR),
      tag) = some (.mulx d hd (.reg s2)) := by
    simp only [wideArgs?, true_or, if_true]
  unfold fstepF stepMemF
  simp only [cmpArgs?, movRegArgs?, lsemStepMem_of_wideArgs hw]
  rw [show carryArgs? ((.Lopn [.reg d, .reg hd] (withWidthTag 64 "MULX") [.reg s2] : LinstrR),
      tag) = none from rfl, hw]

theorem getW_of_lvm {s : LstateN} {r : String} {w : Nat} {v : BitVec w}
    (h : s.lvm r = ⟨w, v⟩) : s.getW r w = some v := by
  unfold LstateN.getW
  split
  · rename_i hw
    congr 1
    revert hw
    rw [h]
    intro hw
    rfl
  · rename_i hw
    rw [h] at hw
    exact absurd rfl hw

theorem ne_of_strip {opn m : String} (hhi : stripWidthTag opn = "MULXHI")
    (hm : stripWidthTag m ≠ "MULXHI") : opn ≠ m := fun h => hm (h ▸ hhi)

/-- The source `MULXHI hd, [h1, s2]` on two width-`64` sources writes the high word of the
    product to `hd`. -/
theorem fstepF_mulhi (hd h1 s2 opn : String) (cd : Option Nat)
    (hhi : stripWidthTag opn = "MULXHI") (s : LstateM) (zf : Bool) {x y : BitVec 64}
    (hx : s.reg.lvm h1 = ⟨64, x⟩) (hy : s.reg.lvm s2 = ⟨64, y⟩) :
    fstepF (.Lopn [.reg hd] opn [.reg h1, .reg s2], .reg cd) s zf
      = some ((s.setReg hd (mulHiW x y)).nextPc, zf) := by
  have hc : cmpArgs? ((.Lopn [.reg hd] opn [.reg h1, .reg s2] : LinstrR), MemTag.reg cd)
      = none := by
    simp only [cmpArgs?]; rw [if_neg (ne_of_strip hhi (by decide))]
  have ha : aluFlagOp? ((.Lopn [.reg hd] opn [.reg h1, .reg s2] : LinstrR), MemTag.reg cd)
      = none := by
    simp only [aluFlagOp?]
    rw [if_neg (ne_of_strip hhi (by decide)), if_neg (ne_of_strip hhi (by decide)),
      if_neg (ne_of_strip hhi (by decide)), if_neg (ne_of_strip hhi (by decide)),
      if_neg (ne_of_strip hhi (by decide))]
  have hmc : lsemStepMC (.Lopn [.reg hd] opn [.reg h1, .reg s2]) s.reg
      = some ((s.reg.setReg hd (mulHiW x y)).nextPc) := by
    simp [lsemStepMC, mulhiStruct?, hhi, readReg, hx, getW_of_lvm hy]
  unfold fstepF stepMemF
  rw [hc]
  simp only [movRegArgs?]
  rw [lsemStepMem_reg, lsemStepCast_of_delegate _ _
    (Or.inl ⟨rfl, by simp [movImmStruct?]⟩), hmc]
  simp only [Option.map_some, withALUFlags_of_none ha]
  rfl

/-- **The fused site.** When the low destination `d` holds the low word of the product of
    the two width-`64` sources of `MULXHI hd, [h1, s2]`, the fused sequence runs from an
    agreeing base to a base that agrees with the source step's result. -/
theorem site_sim {d hd h1 s2 opn : String} {cd : Option Nat}
    (hhi : stripWidthTag opn = "MULXHI") (hkd : KeptN d) (hkh1 : KeptN h1) (hks2 : KeptN s2)
    (hkhd : KeptN hd) (hdR : d ≠ "RDX") (hhdR : hd ≠ "RDX") (hs2R : s2 ≠ "RDX")
    {s s' t : LstateM} {zf zt : Bool} {x y : BitVec 64}
    (hA : Agree s s') (hx : s.reg.lvm h1 = ⟨64, x⟩) (hy : s.reg.lvm s2 = ⟨64, y⟩)
    (hlo : s.reg.lvm d = ⟨64, x * y⟩)
    (h : fstepF (.Lopn [.reg hd] opn [.reg h1, .reg s2], .reg cd) s zf = some (t, zt)) :
    ∃ t', runStraightF (fuseSiteExp d (.Lopn [.reg hd] opn [.reg h1, .reg s2], .reg cd)) s' zf
      = some (t', zt) ∧ Agree t t' := by
  rw [fstepF_mulhi hd h1 s2 opn cd hhi s zf hx hy] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hx' : s'.reg.lvm h1 = ⟨64, x⟩ := (hA.reg h1 hkh1).trans hx
  have hy' : s'.reg.lvm s2 = ⟨64, y⟩ := (hA.reg s2 hks2).trans hy
  simp only [fuseSiteExp, runStraightF_cons, fstepF_saveRdx, Option.bind_some, fstepF_pinRdx,
    fstepF_mulx64]
  have e1 : ((s'.setReg "R15" (s'.reg.lvm "RDX").snd).nextPc).reg.lvm h1 = ⟨64, x⟩ := by
    have hk1 : h1 ≠ "R15" := hkh1
    simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, hk1, hx']
  rw [e1]
  have g1 : (((s'.setReg "R15" (s'.reg.lvm "RDX").snd).nextPc.setReg "RDX"
      (⟨64, x⟩ : (Σ w, BitVec w)).snd).nextPc).reg.getW "RDX" 64 = some x :=
    getW_of_lvm (by simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc])
  have g2 : (((s'.setReg "R15" (s'.reg.lvm "RDX").snd).nextPc.setReg "RDX"
      (⟨64, x⟩ : (Σ w, BitVec w)).snd).nextPc).reg.getW s2 64 = some y :=
    getW_of_lvm (by
      have hk2 : s2 ≠ "R15" := hks2
      simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, hk2, hs2R, hy'])
  simp only [wideStep, evalOperandN, mulxSrc, g1, g2, Option.map_some, Option.bind_some,
    fstepF_restoreRdx, runStraightF_nil]
  refine ⟨_, rfl, ⟨fun r hr => ?_, fun r hr => hA.arr r hr, hA.mem, hA.cf, hA.of⟩⟩
  have hhi' : mulHiW x y = (X86Backend.Jasmin.x86_MULX_lo_hi x y).2 := rfl
  by_cases hrx : r = "RDX"
  · subst hrx
    have hk : KeptN "RDX" := by simp [KeptN]
    simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, Ne.symm hhdR,
      Ne.symm hkhd, Ne.symm hkd, hA.reg "RDX" hk]
  simp only [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, if_neg hr,
    if_neg hrx]
  by_cases hrh : r = hd
  · simp [hrh, hhi']
  · rw [if_neg hrh, if_neg hrh]
    by_cases hrd : r = d
    · subst hrd
      rw [if_pos rfl, hlo, X86Backend.FuseMulHi.mulx_lo_eq_mul]
    · rw [if_neg hrd]
      exact hA.reg r hr

end Steps

/-! ## 5. The analysis of the source body

The symbolic step `OwnedLprogTV.symStep` describes a step of the flag machine exactly.
Run over the source body from the last control instruction, it gives at each position a
symbolic state whose description of the actual state is the invariant of the simulation;
the decided check `fuseOKL` reads off it, at each fused site, that the low destination
holds the low word of the product of the two sources and that both sources have width
`64`. -/

section Analysis

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV

/-- A symbolic state extended by one instruction, with the guards accumulated. -/
def symSnoc (o : SOut) (i : LinstrRM) : SOut :=
  match o with
  | .ok ss g =>
      match symStep i ss with
      | .ok ss1 g1 => .ok ss1 (g ++ g1)
      | .fail => .fail
      | .unk => .unk
  | .fail => .fail
  | .unk => .unk

/-- The instruction is not an `Lopn`, or it is the shadow instruction of a call: the
    analysis of the block restarts after it. -/
def isCtlB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ _ _ => (shadowCall? i.1).isSome
  | _ => true

/-- The position of the first instruction after the last control instruction before `k`. -/
def bstart (c : List LinstrRM) : Nat → Nat
  | 0 => 0
  | k + 1 => if ((c[k]?).map isCtlB).getD false then k + 1 else bstart c k

/-- The symbolic state at position `k`: the instructions from `bstart c k` to `k`, run from
    the start state. -/
def blk (c : List LinstrRM) (k : Nat) : SOut :=
  ((c.drop (bstart c k)).take (k - bstart c k)).foldl symSnoc (.ok SSt.start [])

theorem bstart_le (c : List LinstrRM) : ∀ k, bstart c k ≤ k
  | 0 => le_refl _
  | k + 1 => by
      unfold bstart
      split
      · exact le_refl _
      · exact Nat.le_succ_of_le (bstart_le c k)

theorem blk_zero (c : List LinstrRM) : blk c 0 = .ok SSt.start [] := by
  simp [blk, bstart]

theorem blk_succ_ctl {c : List LinstrRM} {k : Nat} {i : LinstrRM} (hk : c[k]? = some i)
    (hc : isCtlB i = true) : blk c (k + 1) = .ok SSt.start [] := by
  have : bstart c (k + 1) = k + 1 := by simp [bstart, hk, hc]
  simp [blk, this]

theorem blk_succ_lopn {c : List LinstrRM} {k : Nat} {i : LinstrRM} (hk : c[k]? = some i)
    (hc : isCtlB i = false) : blk c (k + 1) = symSnoc (blk c k) i := by
  have hb : bstart c (k + 1) = bstart c k := by simp [bstart, hk, hc]
  have hle := bstart_le c k
  unfold blk
  rw [hb, show k + 1 - bstart c k = (k - bstart c k) + 1 by omega, List.take_add_one,
    List.getElem?_drop, show bstart c k + (k - bstart c k) = k by omega, hk, Option.toList_some,
    List.foldl_append]
  rfl

/-- A symbolic word of width `64`: its width-fixing word has a known width `64`, or is a
    start register of `E`. -/
def w64 (E : List String) (t : STerm) : Bool :=
  t.wbase.wknown == some 64 || (match t.wbase with | .reg x => E.contains x | _ => false)

theorem w64_sound {E : List String} {V : String → Σ w, BitVec w} {A : String → ArrCell}
    {C O : Bool} (hV : ∀ x ∈ E, (V x).1 = 64) {t : STerm} (h : w64 E t = true) :
    (t.ev V A C O).1 = 64 := by
  rw [← STerm.wbase_ev]
  unfold w64 at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · exact STerm.wknown_ev V A C O (by simpa using h)
  · revert h
    cases t.wbase with
    | reg x => intro h; exact hV x (by simpa using h)
    | _ => intro h; simp at h

/-- The symbolic low word of the product of `a` and `b`, in either order. -/
def mulLoB (dt a b : STerm) : Bool :=
  dt == .bin "MUL" a b || dt == .bin "MUL" b a || dt == .mulx false a b

theorem mulLoB_sound {V : String → Σ w, BitVec w} {A : String → ArrCell} {C O : Bool}
    {dt a b : STerm} {x y : BitVec 64} (h : mulLoB dt a b = true)
    (ha : a.ev V A C O = ⟨64, x⟩) (hb : b.ev V A C O = ⟨64, y⟩) :
    dt.ev V A C O = ⟨64, x * y⟩ := by
  have hne : ("MUL" = "MULXHI") = False := by simp
  unfold mulLoB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · rw [STerm.ev, ha, hb]
    simp [binW, extW, applyOpnN, hne]
  · rw [STerm.ev, ha, hb]
    simp [binW, extW, applyOpnN, hne, BitVec.mul_comm]
  · rw [STerm.ev, ha, hb]
    simp [castW, X86Backend.FuseMulHi.mulx_lo_eq_mul]

/-- The check of a fused site with low destination `d` on the symbolic state `ss` before
    it: a register-tagged `MULXHI hd, [h1, s2]` whose sources have width `64` and whose
    low destination, no reload scratch and not `RDX`, holds the low word of their product. -/
def siteOK (E : List String) (d : String) (i : LinstrRM) (ss : SSt) : Bool :=
  match i with
  | (.Lopn [.reg _] opn [.reg h1, .reg s2], .reg _) =>
      stripWidthTag opn == "MULXHI" && (nameOK d && d != "RDX") && w64 E (ss.regs h1)
        && w64 E (ss.regs s2)
        && mulLoB (ss.regs d) (ss.regs h1) (ss.regs s2)
  | _ => false

/-- The instruction classes the simulation covers: an `Lopn`, a label, a zero-flag
    conditional or a goto. -/
def clsB (i : LinstrRM) : Bool :=
  match i.1 with
  | .Lopn _ _ _ => true
  | .Llabel _ _ => true
  | .Lcond _ _ => (flagCondCC? i).isSome
  | .Lgoto _ => true
  | _ => false

/-- The check at position `k`: the symbolic state is described (not outside the fragment),
    gives every register of `E` a word of width `64` when the registers of `E` have width `64`
    at the start of the block (`w64`), and a fused site passes `siteOK`. -/
def posOK (E : List String) (L : List (Option String)) (c : List LinstrRM) (k : Nat) : Bool :=
  match blk c k with
  | .ok ss _ =>
      E.all (fun x => w64 E (ss.regs x)) &&
        (match L[k]? with
         | some (some d) => (c[k]?).any (fun i => siteOK E d i ss)
         | _ => true)
  | .fail => true
  | .unk => false

/-- **The check of the fusion's side conditions**, on the source body `c` with the low
    destinations `L` and the width-`64` start registers `E`: every instruction is in the
    covered classes, leaves the fusion's names alone and is not a `MULX`, and every
    position passes `posOK`. -/
def fuseOKL (E : List String) (L : List (Option String)) (c : List LinstrRM) : Bool :=
  c.all (fun i => clsB i && wireOK i.1 && JasminLsemExportRewrites.mulxFree i)
    && (List.range (c.length + 1)).all (posOK E L c)

/-- Every register of `E` holds a width-`64` word. -/
def E64 (E : List String) (s : LstateM) : Prop := ∀ x ∈ E, (s.reg.lvm x).1 = 64

/-- The invariant of the simulation at position `k`: the registers of `E` have width `64`,
    and the symbolic state `blk c k` describes the base, for start registers whose `E`
    entries have width `64`, with its guards holding. -/
def FInv (E : List String) (c : List LinstrRM) (k : Nat) (s : LstateM) (z : Bool) : Prop :=
  E64 E s ∧
    match blk c k with
    | .ok ss gs => ∃ (V : String → Σ w, BitVec w) (A : String → ArrCell) (C O Z : Bool),
        (∀ x ∈ E, (V x).1 = 64) ∧ AllG V A C O gs
          ∧ Holds V A C O Z ss { prog := { base := s, lfn := "" }, zf := z }
    | _ => False

theorem posOK_of {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) {k : Nat} (hk : k ≤ c.length) : posOK E L c k = true :=
  List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).2 k (by simp; omega)

theorem instr_of {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) {k : Nat} {i : LinstrRM} (hk : c[k]? = some i) :
    clsB i = true ∧ wireOK i.1 = true ∧ JasminLsemExportRewrites.mulxFree i = true := by
  have := List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).1 i (List.mem_of_getElem? hk)
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem finv_start (E : List String) (c : List LinstrRM) (k : Nat) (s : LstateM) (z : Bool)
    (hb : blk c k = .ok SSt.start []) (hE : E64 E s) : FInv E c k s z := by
  refine ⟨hE, ?_⟩
  rw [hb]
  exact ⟨s.reg.lvm, s.larr, s.cf, s.of, z, hE, allG_nil _ _ _ _,
    holds_start { prog := { base := s, lfn := "" }, zf := z }⟩

/-- The invariant is kept by a source step of an `Lopn`. -/
theorem finv_step {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) {k : Nat} {i : LinstrRM} (hk : c[k]? = some i)
    (hl : IsLopn i) {s t : LstateM} {z zt : Bool} (hI : FInv E c k s z)
    (hst : fstepF i s z = some (t, zt)) : FInv E c (k + 1) t zt := by
  have hsh : shadowCall? i.1 = none := by
    by_contra hn
    have he := evalInstrPMemF_shadowCall emptyP i { prog := { base := s, lfn := "" }, zf := z } hn
    rw [evalInstrPMemF_isLopn _ i _ hl] at he
    change (fstepF i s z).map _ = none at he
    rw [hst] at he
    cases he
  have hc : isCtlB i = false := by
    obtain ⟨d, o, s0, hd⟩ := hl
    simp only [isCtlB, hd, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    rw [← hd]
    exact hsh
  have hlen : k + 1 ≤ c.length := (List.getElem?_eq_some_iff.mp hk).1
  have hpos := posOK_of h hlen
  obtain ⟨-, hI⟩ := hI
  have hb := blk_succ_lopn hk hc
  cases hk0 : blk c k with
  | fail => rw [hk0] at hI; exact hI.elim
  | unk => rw [hk0] at hI; exact hI.elim
  | ok ss gs =>
      rw [hk0] at hI
      obtain ⟨V, A, C, O, Z, hV, hg, hH⟩ := hI
      have hsnd := symStep_sound emptyP i ss V A C O Z _ hH
      have hev : evalInstrPMemF emptyP i { prog := { base := s, lfn := "" }, zf := z }
          = some { prog := { base := t, lfn := "" }, zf := zt } := by
        rw [evalInstrPMemF_isLopn _ i _ hl]
        show (fstepF i s z).map _ = _
        rw [hst]; rfl
      rw [hev] at hsnd
      rw [hk0] at hb
      cases hs : symStep i ss with
      | ok ss1 g1 =>
          rw [hs] at hsnd
          obtain ⟨hg1, hH1, -⟩ := hsnd.1 _ rfl
          have hb' : blk c (k + 1) = .ok ss1 (gs ++ g1) := by rw [hb, symSnoc, hs]
          unfold posOK at hpos
          rw [hb'] at hpos
          have hE : ∀ x ∈ E, w64 E (ss1.regs x) = true := fun x hx =>
            List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ hpos).1 x hx
          refine ⟨fun x hx => ?_, ?_⟩
          · have := hH1.1 x
            simp only at this
            rw [this]
            exact w64_sound hV (hE x hx)
          · rw [hb']
            exact ⟨V, A, C, O, Z, hV, allG_append.mpr ⟨hg, hg1⟩, hH1⟩
      | fail =>
          rw [hs] at hsnd
          exact absurd hsnd (by simp [SOut.Desc])
      | unk =>
          have hb' : blk c (k + 1) = .unk := by rw [hb, symSnoc, hs]
          unfold posOK at hpos
          rw [hb'] at hpos
          exact absurd hpos (by simp)

end Analysis

/-! ## 6. The fusion preserves halting runs -/

section Main

open CatCrypt.Crypto.SecureCompilation.X86Backend.OwnedLprogTV
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemExportRewrites (instrNames opNames mulxFree)

theorem fuseE_of_not_lopn {L : List (Option String)} {k : Nat} {i : LinstrRM}
    (h : ¬ IsLopn i) : fuseE L k i = [i] := by
  unfold fuseE fuseSiteExp
  split
  · split
    · rename_i hd _ _ _ _ he
      exact absurd ⟨_, _, _, he⟩ h
    · rfl
  · rfl

theorem fuseE_isLopn {L : List (Option String)} {k : Nat} {i : LinstrRM} (hl : IsLopn i) :
    ∀ j ∈ fuseE L k i, IsLopn j := by
  intro j hj
  unfold fuseE fuseSiteExp at hj
  split at hj
  · split at hj
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> exact ⟨_, _, _, rfl⟩
    · rw [List.mem_singleton.mp hj]; exact hl
  · rw [List.mem_singleton.mp hj]; exact hl

theorem length_fuseE_le (L : List (Option String)) (k : Nat) (i : LinstrRM) :
    (fuseE L k i).length ≤ 4 := by
  unfold fuseE fuseSiteExp
  split
  · split <;> simp
  · simp

theorem clsB_spec {i : LinstrRM} (h : clsB i = true) : IsLopn i ∨ CtlI i := by
  obtain ⟨w, tag⟩ := i
  cases w with
  | Lopn d o s => exact Or.inl ⟨d, o, s, rfl⟩
  | Llabel kd l => exact Or.inr (Or.inl ⟨kd, l, rfl⟩)
  | Lcond c l =>
      refine Or.inr (Or.inr (Or.inl ⟨c, l, rfl, fun hn => ?_⟩))
      simp [clsB, hn] at h
  | Lgoto tgt => exact Or.inr (Or.inr (Or.inr ⟨tgt, rfl⟩))
  | _ => simp [clsB] at h

theorem keptN_of_nameOK {n : String} (h : nameOK n = true) : KeptN n := by
  simp only [nameOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.1

theorem width64 (p : Σ w, BitVec w) (h : p.1 = 64) : ∃ x : BitVec 64, p = ⟨64, x⟩ := by
  obtain ⟨w, v⟩ := p
  simp only at h
  subst h
  exact ⟨v, rfl⟩

/-- The expansion simulation conditions hold for a body that passes `fuseOKL`. -/
theorem expInv_fuse {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) : ExpInv Agree (E64 E) (FInv E c) (fuseE L) c where
  cls k i hk := by
    rcases clsB_spec (instr_of h hk).1 with hl | hc
    · exact Or.inl hl
    · refine Or.inr ⟨hc, fuseE_of_not_lopn ?_⟩
      rintro ⟨d, o, s, hd⟩
      rcases hc with ⟨_, _, he⟩ | ⟨_, _, he, _⟩ | ⟨_, he⟩ <;> rw [hd] at he <;> cases he
  lopn k i hk hl := by
    refine ⟨fuseE_isLopn hl, fun s s' t zf zt hI hA hst => ⟨finv_step h hk hl hI hst, ?_⟩⟩
    obtain ⟨-, hw, hm⟩ := instr_of h hk
    have hkept : ∀ n ∈ instrNames i.1, KeptN n := fun n hn =>
      keptN_of_nameOK (nameOK_of_mem hw hn)
    cases hL : L[k]? with
    | some lo =>
        cases lo with
        | some d =>
            have hlen : k ≤ c.length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp hk).1
            have hpos := posOK_of h hlen
            obtain ⟨hE, hI⟩ := hI
            unfold posOK at hpos
            cases hb : blk c k with
            | fail => rw [hb] at hI; exact hI.elim
            | unk => rw [hb] at hI; exact hI.elim
            | ok ss gs =>
                rw [hb] at hI hpos
                obtain ⟨V, A, C, O, Z, hV, -, hH⟩ := hI
                rw [hL, hk] at hpos
                have hsite : siteOK E d i ss = true := (by simpa using hpos : _ ∧ _).2
                have hfe : fuseE L k i = fuseSiteExp d i := by simp [fuseE, hL]
                rw [hfe]
                obtain ⟨wire, tag⟩ := i
                unfold siteOK at hsite
                split at hsite
                · rename_i hd opn h1 s2 cd heq
                  simp only [Prod.mk.injEq] at heq
                  obtain ⟨rfl, rfl⟩ := heq
                  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsite
                  obtain ⟨⟨⟨⟨hhi, hdn, hdR⟩, hw1⟩, hw2⟩, hmul⟩ := hsite
                  have hmo := mulOK_spill (mulOK_of_wireOK hw)
                    (by simp [X86Backend.FuseMulHi.isMulHiMnem, hhi] :
                      (X86Backend.FuseMulHi.isLowMulMnem opn
                        || X86Backend.FuseMulHi.isMulHiMnem opn) = true)
                  have hr : ∀ q, s.reg.lvm q = (ss.regs q).ev V A C O := hH.1
                  obtain ⟨x, hx⟩ := width64 _ (w64_sound (A := A) (C := C) (O := O) hV hw1)
                  obtain ⟨y, hy⟩ := width64 _ (w64_sound (A := A) (C := C) (O := O) hV hw2)
                  have hlo := mulLoB_sound hmul hx hy
                  have hn1 : KeptN h1 := hkept h1 (by simp [instrNames, opNames])
                  have hn2 : KeptN s2 := hkept s2 (by simp [instrNames, opNames])
                  have hnh : KeptN hd := hkept hd (by simp [instrNames, opNames])
                  exact site_sim hhi (keptN_of_nameOK hdn) hn1 hn2 hnh hdR hmo.2.2.1 hmo.2.2.2 hA
                    ((hr h1).trans hx) ((hr s2).trans hy) ((hr d).trans hlo) hst
                · simp at hsite
        | none =>
            have hfe : fuseE L k i = [i] := by simp [fuseE, hL]
            rw [hfe]
            obtain ⟨t', h', hA'⟩ := fstepF_agree hl hkept hm hA hst
            exact ⟨t', by rw [runStraightF_cons, h']; rfl, hA'⟩
    | none =>
        have hfe : fuseE L k i = [i] := by simp [fuseE, hL]
        rw [hfe]
        obtain ⟨t', h', hA'⟩ := fstepF_agree hl hkept hm hA hst
        exact ⟨t', by rw [runStraightF_cons, h']; rfl, hA'⟩
  ginv _ _ _ hI := hI.1
  gpc _ _ hG := hG
  start k i hk hc s z hG := by
    have hctl : isCtlB i = true := by
      obtain ⟨w, tag⟩ := i
      rcases hc with ⟨_, _, he⟩ | ⟨_, _, he, _⟩ | ⟨_, he⟩ <;> simp only at he <;> subst he <;> rfl
    exact finv_start E c (k + 1) s z (blk_succ_ctl hk hctl) hG
  qpc _ _ p q hA := hA.setLpc p q

/-- **The fusion preserves halting runs (by position).** For a source body `c` and low
    destinations `L` that pass `fuseOKL E L c`, every halting run of `c` from program
    counter `0`, from a base whose registers in `E` have width `64`, is matched by a
    halting run of the expanded body from the same state, with at most four times the
    fuel; the final states agree on every register and array other than `R15`, on the word
    memory, the carry, overflow and zero flags and the function name. -/
theorem lsemFuelMemF_fuseOKL {E : List String} {L : List (Option String)}
    {c : List LinstrRM} (h : fuseOKL E L c = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (expI (fuseE L) c 0)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  have hR : RelI Agree (FInv E c) (fuseE L) c s s := by
    refine ⟨rfl, rfl, ?_, Agree.refl _, ?_⟩
    · rw [hpc]; rfl
    · rw [hpc]
      exact finv_start E c 0 _ _ (blk_zero c) hE
  obtain ⟨fuel', t', hf, hrun', hRt⟩ :=
    lsemFuelMemF_expI (expInv_fuse h) (fun k i _ => length_fuseE_le L k i) fuel hR hrun
  exact ⟨fuel', t', hf, hrun', hRt.base, hRt.zf, hRt.lfn⟩

/-- The check of the fusion `fuseMulHiRM` on a source body, with the width-`64` start
    registers `E`. -/
def fuseMulHiOK (E : List String) (c : List LinstrRM) : Bool := fuseOKL E (fuseLo c) c

theorem wireOK_of_fuseOKL {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) : ∀ i ∈ c, wireOK i.1 = true := fun _ hi =>
  let ⟨_, hk⟩ := List.getElem?_of_mem hi
  (instr_of h hk).2.1

/-- **`fuseMulHi_lsemFuelMemF`: the looped-body `MULX` fusion preserves halting runs.** For a
    typed body `c` that passes `fuseMulHiOK E c`, every halting run of `c` from program
    counter `0`, from a base whose registers in `E` have width `64`, is matched by a halting
    run of `fuseMulHiRM c` from the same state, with at most four times the fuel; the final
    states agree on every register and array other than `R15`, on the word memory, the carry, overflow and zero flags and the function name. -/
theorem fuseMulHi_lsemFuelMemF {E : List String} {c : List LinstrRM}
    (h : fuseMulHiOK E c = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (fuseMulHiRM c)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  rw [fuseMulHiRM_eq c (wireOK_of_fuseOKL h)]
  exact lsemFuelMemF_fuseOKL h fn s t hpc hE fuel hrun

theorem expI_fuseE_none {L : List (Option String)} :
    ∀ (xs : List LinstrRM) (n : Nat), (∀ k, k < xs.length → L[n + k]? = some none) →
      expI (fuseE L) xs n = xs
  | [], _, _ => rfl
  | _ :: xs, n, h => by
      have h0 := h 0 (by simp)
      rw [Nat.add_zero] at h0
      rw [expI, expI_fuseE_none xs (n + 1) (fun k hk => by
        rw [show n + 1 + k = n + (k + 1) by omega]; exact h (k + 1) (by simp; omega))]
      simp [fuseE, h0]

theorem expI_fuseE_shift {L L' : List (Option String)} (m : Nat)
    (hL : ∀ k, L[m + k]? = L'[k]?) :
    ∀ (xs : List LinstrRM) (n : Nat), expI (fuseE L) xs (m + n) = expI (fuseE L') xs n
  | [], _ => rfl
  | i :: xs, n => by
      rw [expI, expI, show m + n + 1 = m + (n + 1) by omega, expI_fuseE_shift m hL xs (n + 1)]
      simp only [fuseE, hL n]

/-- The low destinations of a body `pre ++ loop` whose loop part alone is fused. -/
def fuseLoPre (pre loop : List LinstrRM) : List (Option String) :=
  List.replicate pre.length none ++ fuseLo loop

/-- **The fusion of the loop part of a body.** For a typed body `pre ++ loop` that passes
    `fuseOKL E (fuseLoPre pre loop)`, every halting run from program counter `0`, from a
    base whose registers in `E` have width `64`, is matched by a halting run of
    `pre ++ fuseMulHiRM loop` from the same state, with at most four times the fuel; the
    final states agree as in `fuseMulHi_lsemFuelMemF`. -/
theorem fuseMulHi_lsemFuelMemF_pre {E : List String} {pre loop : List LinstrRM}
    (h : fuseOKL E (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ lsemFuelMemF (singletonProgM fn (pre ++ fuseMulHiRM loop)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  have hw : ∀ i ∈ loop, wireOK i.1 = true := fun i hi =>
    wireOK_of_fuseOKL h i (List.mem_append_right _ hi)
  have heq : expI (fuseE (fuseLoPre pre loop)) (pre ++ loop) 0 = pre ++ fuseMulHiRM loop := by
    rw [expI_append, Nat.zero_add, fuseMulHiRM_eq loop hw]
    congr 1
    · exact expI_fuseE_none pre 0 (fun k hk => by
        rw [Nat.zero_add, fuseLoPre,
          List.getElem?_append_left (by rw [List.length_replicate]; exact hk)]
        simp [hk])
    · have := expI_fuseE_shift (L := fuseLoPre pre loop) (L' := fuseLo loop) pre.length
        (fun k => by simp [fuseLoPre, List.getElem?_append_right]) loop 0
      rwa [Nat.add_zero] at this
  rw [← heq]
  exact lsemFuelMemF_fuseOKL h fn s t hpc hE fuel hrun

/-! ## 7. The fusion at an instruction set with local calls -/

/-- No instruction of the expansion of an instruction that is no shadow instruction of a
    call is the shadow instruction of a call. -/
theorem fuseE_shadowCall {L : List (Option String)} {k : Nat} {i : LinstrRM}
    (hi : shadowCall? i.1 = none) : ∀ j ∈ fuseE L k i, shadowCall? j.1 = none := by
  intro j hj
  unfold fuseE fuseSiteExp at hj
  split at hj
  · split at hj
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> rfl
    · rw [List.mem_singleton.mp hj]; exact hi
  · rw [List.mem_singleton.mp hj]; exact hi

/-- A shadow instruction of a call at a position without a fused site expands to itself. -/
theorem fuseE_call {L : List (Option String)} {c : List LinstrRM}
    (hL : ∀ (k : Nat) (i : LinstrRM) (d : String), c[k]? = some i → L[k]? = some (some d) →
      shadowCall? i.1 = none)
    {k : Nat} {i : LinstrRM} (hk : c[k]? = some i) (hsh : shadowCall? i.1 ≠ none) :
    fuseE L k i = [i] := by
  unfold fuseE
  split
  · rename_i d hd
    exact absurd (hL k i d hk hd) hsh
  · rfl

theorem e64_setReg {E : List String} {s : LstateM} (h : E64 E s) (dst : String)
    (r : BitVec 64) : E64 E (s.setReg dst r).nextPc := by
  intro x hx
  by_cases hxd : x = dst
  · subst hxd
    simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg]
  · simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, hxd, h x hx]

theorem Agree.setReg {a b : LstateM} (h : Agree a b) (dst : String) (r : BitVec 64) :
    Agree (a.setReg dst r).nextPc (b.setReg dst r).nextPc := by
  refine ⟨fun x hx => ?_, h.arr, h.mem, h.cf, h.of⟩
  by_cases hxd : x = dst
  · subst hxd
    simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg]
  · simp [LstateM.setReg, LstateM.nextPc, LstateN.nextPc, LstateN.lvm_setReg, hxd, h.reg x hx]

/-- Operand words read at width `64` depend only on the registers the operands name. -/
theorem mapM_evalOperandN_congr {s s' : LstateN} :
    ∀ (srcs : List LOperand), (∀ n ∈ srcs.flatMap opNames, s'.lvm n = s.lvm n) →
      srcs.mapM (evalOperandN s' 64) = srcs.mapM (evalOperandN s 64)
  | [], _ => rfl
  | o :: os, h => by
      have ho : evalOperandN s' 64 o = evalOperandN s 64 o := by
        cases o with
        | reg n =>
            simp only [evalOperandN, LstateN.getW]
            rw [h n (by simp [opNames])]
        | _ => rfl
      have hos : ∀ n ∈ os.flatMap opNames, s'.lvm n = s.lvm n := fun n hn =>
        h n (List.mem_flatMap.mpr (by
          obtain ⟨a, ha, hna⟩ := List.mem_flatMap.mp hn
          exact ⟨a, List.mem_cons_of_mem _ ha, hna⟩))
      rw [List.mapM_cons, List.mapM_cons, ho, mapM_evalOperandN_congr os hos]

theorem Agree.setArr {a b : LstateM} (h : Agree a b) (dst : String) {n : Nat}
    (v : Fin n → BitVec 64) : Agree (a.setArr dst v).nextPc (b.setArr dst v).nextPc := by
  refine ⟨fun x hx => h.reg x hx, fun x hx => ?_, h.mem, h.cf, h.of⟩
  simp only [LstateM.larr_nextPc, LstateM.larr_setArr]
  split
  · rfl
  · exact h.arr x hx

/-- Argument words at the array positions `a` read only the registers and the arrays the
    operands name. -/
theorem argsRead_congr_names (a : Nat → Option Nat) {b b' : LstateM} :
    ∀ (j : Nat) (srcs : List LOperand),
      (∀ n ∈ srcs.flatMap opNames, b'.reg.lvm n = b.reg.lvm n ∧ b'.larr n = b.larr n) →
      argsRead a b' j srcs = argsRead a b j srcs
  | _, [], _ => rfl
  | j, o :: os, h => by
      have ho : argRead a b' j o = argRead a b j o := by
        unfold argRead
        cases o with
        | reg n =>
            have hn := h n (by simp [opNames])
            cases a j with
            | none =>
                simp only [evalOperandN]
                unfold LstateN.getW
                rw [hn.1]
            | some m =>
                simp only
                unfold LstateM.getArr
                rw [hn.2]
        | _ => cases a j <;> rfl
      rw [argsRead, argsRead, ho, argsRead_congr_names a (j + 1) os fun n hn =>
        h n (List.mem_flatMap.mpr (by
          obtain ⟨x, hx, hnx⟩ := List.mem_flatMap.mp hn
          exact ⟨x, List.mem_cons_of_mem _ hx, hnx⟩))]

/-- **A call in a checked body.** At a shadow instruction of a call in a body that passes
    `fuseOKL`, agreeing bases give equal argument words at every choice `a` of array
    positions, and the write of a result, a word or a word array, keeps the invariant,
    which restarts after the call, and keeps the agreement. -/
theorem fuse_call {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (h : fuseOKL E L c = true) {k : Nat} {i : LinstrRM} (hk : c[k]? = some i)
    {dst f : String} {srcs : List LOperand} (hi : i.1 = callShadow dst f srcs)
    (a : Nat → Option Nat) {s s' : LstateMF} (x : CallRes)
    (hI : FInv E c k s.prog.base s.zf) (hA : Agree s.prog.base s'.prog.base) :
    argsRead a s'.prog.base 0 srcs = argsRead a s.prog.base 0 srcs
      ∧ FInv E c (k + 1) (retRes dst x s).prog.base s.zf
      ∧ Agree (retRes dst x s).prog.base (retRes dst x s').prog.base := by
  obtain ⟨-, hw, -⟩ := instr_of h hk
  have hkept : ∀ n ∈ srcs.flatMap opNames, KeptN n := fun n hn =>
    keptN_of_nameOK (nameOK_of_mem hw (by
      rw [hi]
      simp only [callShadow, instrNames, List.flatMap_append, List.mem_append]
      exact Or.inr hn))
  refine ⟨argsRead_congr_names a 0 srcs fun n hn =>
      ⟨hA.reg n (hkept n hn), hA.arr n (hkept n hn)⟩, ?_, ?_⟩
  · have hctl : isCtlB i = true := by
      have hs := LprogIsa.shadowCall?_callShadow dst f srcs
      obtain ⟨w, tag⟩ := i
      simp only at hi
      subst hi
      unfold callShadow at hs
      simp [isCtlB, callShadow, hs]
    have hE : E64 E (retRes dst x s).prog.base := by
      cases x with
      | word r => exact e64_setReg hI.1 dst r
      | arr v => exact fun y hy => hI.1 y hy
    exact finv_start E c (k + 1) _ s.zf (blk_succ_ctl hk hctl) hE
  · cases x with
    | word r => exact hA.setReg dst r
    | arr v => exact hA.setArr dst v

/-- **The fusion at an instruction set with local calls (by position).** The statement of
    `lsemFuelMemF_fuseOKL` for an instruction set `I` whose steps contain those of `x86Isa`
    and whose further steps are local calls, when no fused position holds a shadow
    instruction of a call. -/
theorem lsemFuelMemF_fuseOKL_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {E : List String}
    {L : List (Option String)} {c : List LinstrRM} (h : fuseOKL E L c = true)
    (hL : ∀ (k : Nat) (i : LinstrRM) (d : String), c[k]? = some i → L[k]? = some (some d) →
      shadowCall? i.1 = none)
    (fn : String) (s t : LstateMF) (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base)
    (fuel : Nat) (hrun : I.lsemFuelMemF (singletonProgM fn c) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ I.lsemFuelMemF (singletonProgM fn (expI (fuseE L) c 0)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  have hR : RelI Agree (FInv E c) (fuseE L) c s s := by
    refine ⟨rfl, rfl, ?_, Agree.refl _, ?_⟩
    · rw [hpc]; rfl
    · rw [hpc]
      exact finv_start E c 0 _ _ (blk_zero c) hE
  obtain ⟨fuel', t', hf, hrun', hRt⟩ :=
    lsemFuelMemF_expI_calls hle hcl (expInv_fuse h)
      (fun _ _ _ hsh j hj P x =>
        Isa.CallLocal.step_eq I hle hcl P (fuseE_shadowCall hsh j hj) x)
      (fun _ _ hk hsh _ => ⟨fuseE_call hL hk hsh,
        fun _ f _ hi _ _ x hI hA => fuse_call h hk hi (aa f) x hI hA⟩)
      (fun k i _ => length_fuseE_le L k i) fuel hR hrun
  exact ⟨fuel', t', hf, hrun', hRt.base, hRt.zf, hRt.lfn⟩

/-- A fused position of `fuseLoAux` holds a `MULXHI`, which is no shadow instruction of a
    call. -/
theorem fuseLoAux_site : ∀ (pend : List (String × String)) (xs : List LinstrR) (k : Nat)
    (d : String), (fuseLoAux pend xs)[k]? = some (some d) →
      ∃ w, xs[k]? = some w ∧ shadowCall? w = none
  | _, [], _, _, h => by simp [fuseLoAux] at h
  | pend, w :: rest, k, d, h => by
      have hcons : ∀ k', (∀ pend', (fuseLoAux pend' rest)[k']? = some (some d) →
          ∃ w', rest[k']? = some w' ∧ shadowCall? w' = none) →
          (fuseLoAux pend (w :: rest))[k' + 1]? = some (some d) →
          ∃ w', (w :: rest)[k' + 1]? = some w' ∧ shadowCall? w' = none := by
        intro k' ih h'
        simp only [List.getElem?_cons_succ]
        unfold fuseLoAux at h'
        split at h'
        · split at h'
          · exact ih _ (by simpa using h')
          · split at h'
            · split at h' <;> exact ih _ (by simpa using h')
            · exact ih _ (by simpa using h')
        · exact ih _ (by simpa using h')
      cases k with
      | succ k' => exact hcons k' (fun pend' => fuseLoAux_site pend' rest k' d) h
      | zero =>
          refine ⟨w, rfl, ?_⟩
          unfold fuseLoAux at h
          split at h
          · rename_i dd opn s1 s2
            split at h
            · simp at h
            · split at h
              · rename_i hhi
                by_contra hn
                obtain ⟨dst, opn', srcs, he, hm⟩ := LprogIsaProcs.shadowCall?_wire hn
                cases he
                simp [X86Backend.FuseMulHi.isMulHiMnem,
                  hm.strip_ne "MULXHI" (by decide)] at hhi
              · simp at h
          · simp at h

/-- **The fusion of the loop part of a body at an instruction set with local calls.** The
    statement of `fuseMulHi_lsemFuelMemF_pre` for an instruction set `I` whose steps contain
    those of `x86Isa` and whose further steps are local calls. -/
theorem fuseMulHi_lsemFuelMemF_pre_calls {I : Isa} {aa : String → Nat → Option Nat}
    {ao : String → Option Nat} (hle : x86Isa.StepLe I)
    (hcl : I.CallLocal x86Isa aa ao) {E : List String}
    {pre loop : List LinstrRM}
    (h : fuseOKL E (fuseLoPre pre loop) (pre ++ loop) = true) (fn : String) (s t : LstateMF)
    (hpc : s.prog.base.lpc = 0) (hE : E64 E s.prog.base) (fuel : Nat)
    (hrun : I.lsemFuelMemF (singletonProgM fn (pre ++ loop)) fuel s = some t) :
    ∃ fuel' t', fuel' ≤ fuel * 4
      ∧ I.lsemFuelMemF (singletonProgM fn (pre ++ fuseMulHiRM loop)) fuel' s = some t'
      ∧ Agree t.prog.base t'.prog.base ∧ t'.zf = t.zf ∧ t'.prog.lfn = t.prog.lfn := by
  have hw : ∀ i ∈ loop, wireOK i.1 = true := fun i hi =>
    wireOK_of_fuseOKL h i (List.mem_append_right _ hi)
  have heq : expI (fuseE (fuseLoPre pre loop)) (pre ++ loop) 0 = pre ++ fuseMulHiRM loop := by
    rw [expI_append, Nat.zero_add, fuseMulHiRM_eq loop hw]
    congr 1
    · exact expI_fuseE_none pre 0 (fun k hk => by
        rw [Nat.zero_add, fuseLoPre,
          List.getElem?_append_left (by rw [List.length_replicate]; exact hk)]
        simp [hk])
    · have := expI_fuseE_shift (L := fuseLoPre pre loop) (L' := fuseLo loop) pre.length
        (fun k => by simp [fuseLoPre, List.getElem?_append_right]) loop 0
      rwa [Nat.add_zero] at this
  have hL : ∀ (k : Nat) (i : LinstrRM) (d : String), (pre ++ loop)[k]? = some i → (fuseLoPre pre loop)[k]? = some (some d) →
      shadowCall? i.1 = none := by
    intro k i d hk hd
    by_cases hkp : k < pre.length
    · rw [fuseLoPre, List.getElem?_append_left (by rw [List.length_replicate]; exact hkp)]
        at hd
      simp [hkp] at hd
    · have hkp' : pre.length ≤ k := Nat.le_of_not_lt hkp
      rw [fuseLoPre, List.getElem?_append_right (by rw [List.length_replicate]; exact hkp'),
        List.length_replicate] at hd
      rw [List.getElem?_append_right hkp'] at hk
      obtain ⟨w, hw', hsw⟩ := fuseLoAux_site [] _ _ d hd
      rw [List.getElem?_map, hk] at hw'
      obtain rfl := (Option.some.inj hw').symm
      exact hsw
  rw [← heq]
  exact lsemFuelMemF_fuseOKL_calls hle hcl h hL fn s t hpc hE fuel hrun

end Main

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
