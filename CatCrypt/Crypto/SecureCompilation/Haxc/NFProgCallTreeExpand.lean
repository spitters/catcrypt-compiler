/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi

/-!
# Call trees related to the runs of a body expanded by index

The expansion `JasminLsemFuseMulHi.expI` replaces each instruction of a body by a straight
segment depending on its index; the fusion of the high multiplies `fuseMulHiRM` is one. Its
correctness for halting runs, `JasminLsemFuseMulHi.lsemFuelMemF_expI_calls`, rests on the
relation `RelI` of a state of the body and a state of the expansion, with an invariant indexed
by position. A step of the body on the x86 flag machine is matched by the steps of its
expansion (`expI_step`), and a call, which expands to itself, by the same call when the
invariant and the relation give equal argument words and are kept by the write of every result.
The relation then carries a call tree related to the states of the body by
`NFProgCallTreeExport.TSim` to the states of the expansion (`tsim_expI`), and for the fusion of
the high multiplies (`tsim_fuse`).

## Main results

* `steps_of_runStraightF`: a straight segment of operations held in a program from a position
  on is a run of steps of the program.
* `expI_step`: a step of the body is matched by the steps of its expansion.
* `tsim_expI`: a call tree related to a state of the body is related to every state of the
  expansion that `RelI` relates to it.
* `tsim_fuse`: the same for the fusion of the high multiplies.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExpand

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
open CatCrypt.Crypto.SecureCompilation.X86Backend.X86Isa (x86Isa x86Isa_step)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemFuseMulHi
open CatCrypt.Crypto.SecureCompilation.Ascent.IsaCfg
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (arrArgsOf wordsOf)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (nfCallSig NFCall)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExport (TSim CallOut CallRet)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExportTransfer (TSim.transfer
  steps_sim_of_step)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeWebs (callResOf callOut_retRes)

/-- **A straight segment of operations is a run of steps.** A segment of operations held in the
    program `P` from the position of `b₀` on, at whose instructions the step of `I` is the step
    of `x86Isa`, that `runStraightF` runs from `b₀` to `b₁`, is a run of as many steps of `I`. -/
theorem steps_of_runStraightF {I : Isa} (P : LprogM) (fn : String) (hfn : fn = P.lfn) :
    ∀ (seg : List LinstrRM) (b₀ : LstateM) (zf : Bool) (b₁ : LstateM) (z₁ : Bool),
      (∀ i ∈ seg, IsLopn i) →
      (∀ i ∈ seg, ∀ (Q : LprogM) (s : LstateMF), I.step Q i s = x86Isa.step Q i s) →
      (∀ k, k < seg.length → P.body[b₀.lpc + k]? = seg[k]?) →
      runStraightF seg b₀ zf = some (b₁, z₁) →
      Steps I P seg.length { prog := { base := b₀, lfn := fn }, zf := zf }
        { prog := { base := b₁, lfn := fn }, zf := z₁ }
  | [], b₀, zf, b₁, z₁, _, _, _, h => by
      simp only [runStraightF_nil, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Steps.refl I P _
  | i :: is, b₀, zf, b₁, z₁, hlopn, hns, hpos, h => by
      have hi : IsLopn i := hlopn i (by simp)
      rw [runStraightF_cons] at h
      cases hstep : fstepF i b₀ zf with
      | none => rw [hstep] at h; cases h
      | some bz =>
      obtain ⟨b', z'⟩ := bz
      rw [hstep, Option.bind_some] at h
      have hfetch : findInstrMem P
          ({ prog := { base := b₀, lfn := fn }, zf := zf } : LstateMF).prog = some i := by
        show findInstrMem P { base := b₀, lfn := fn } = some i
        unfold findInstrMem
        rw [ite_eq_left (show ({ base := b₀, lfn := fn } : LstatePM).lfn = P.lfn from hfn)]
        have := hpos 0 (by simp)
        simpa using this
      have h1 : Steps I P 1 { prog := { base := b₀, lfn := fn }, zf := zf }
          { prog := { base := b', lfn := fn }, zf := z' } := by
        refine Steps.one ?_
        unfold Isa.lsemStepPMemF
        rw [hfetch]
        show I.step P i _ = _
        rw [hns i (by simp) P, x86Isa_step, evalInstrPMemF_isLopn P i _ hi, hstep]
        rfl
      have hpc : b'.lpc = b₀.lpc + 1 := fstepF_lpc_succ _ _ _ _ _ hstep
      have h2 := steps_of_runStraightF P fn hfn is b' z' b₁ z₁
        (fun j hj => hlopn j (by simp [hj])) (fun j hj => hns j (by simp [hj]))
        (fun k hk => by
          rw [hpc, show b₀.lpc + 1 + k = b₀.lpc + (k + 1) by omega, hpos (k + 1) (by simp; omega)]
          rfl) h
      rw [List.length_cons, Nat.add_comm]
      exact h1.trans h2

section Sim

variable {Q : LstateM → LstateM → Prop} {G : LstateM → Prop}
  {Inv : Nat → LstateM → Bool → Prop} {e : Nat → LinstrRM → List LinstrRM}

/-- **One source step as steps of the expansion.** A successful source step at instruction `i`
    is matched by a run of steps of an instruction set `I` on the expansion from a related state
    into a related state, when the step of `I` at every instruction of the expansion is the
    step of `x86Isa`. -/
theorem evalInstrPMemF_expI_steps {I : Isa} {fn : String} {body : List LinstrRM}
    (h : ExpInv Q G Inv e body)
    {s s' u : LstateMF} {i : LinstrRM} (hR : RelI Q Inv e body s s')
    (hfn : s.prog.lfn = fn) (hget : body[s.prog.base.lpc]? = some i)
    (hag : ∀ j ∈ e s.prog.base.lpc i, ∀ (P : LprogM) (x : LstateMF),
      I.step P j x = x86Isa.step P j x)
    (he : evalInstrPMemF (singletonProgM fn body) i s = some u) :
    ∃ k u', Steps I (singletonProgM fn (expI e body 0)) k s' u'
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
    refine ⟨(e k i).length, { prog := { base := b', lfn := s'.prog.lfn }, zf := z }, ?_, ?_⟩
    · rw [← hR.zf] at hb'
      exact steps_of_runStraightF (singletonProgM fn (expI e body 0)) s'.prog.lfn hfn'
        (e k i) s'.prog.base s'.zf b' z hex hag hpos hb'
    · have h1 := runStraightF_lpc _ _ _ _ _ hb'
      have h2 := fstepF_lpc_succ _ _ _ _ _ hb
      refine ⟨hR.lfn, rfl, ?_, hQb, ?_⟩
      · show b'.lpc = pcI e body b.lpc
        rw [h1, h2, pcI_succ e hget, hR.pc]
      · show Inv b.lpc b z
        rw [h2]; exact hinv
  · have hfetch : findInstrMem (singletonProgM fn (expI e body 0)) s'.prog = some i := by
      unfold findInstrMem
      rw [ite_eq_left (show s'.prog.lfn = (singletonProgM fn (expI e body 0)).lfn from hfn')]
      have := hpos 0 (by rw [hself]; simp)
      simpa [hself, singletonProgM] using this
    have hone : ∀ {u' : LstateMF},
        evalInstrPMemF (singletonProgM fn (expI e body 0)) i s' = some u' →
        Steps I (singletonProgM fn (expI e body 0)) 1 s' u' := by
      intro u' hu'
      have hI : I.step (singletonProgM fn (expI e body 0)) i s' = some u' := by
        rw [hag i (by rw [hself]; exact List.mem_singleton_self i)]
        exact hu'
      exact Steps.one (by unfold Isa.lsemStepPMemF; rw [hfetch]; exact hI)
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
      exact ⟨1, _, hone (evalInstrPMemF_label _ kd l tag s'),
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
            refine ⟨1, { s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [ite_eq_left (hR.zf.trans hz), hq']; rfl
          · rename_i hz
            cases he
            refine ⟨1, { s' with prog := { s'.prog with base := s'.prog.base.nextPc } },
              hone ?_, ⟨hR.lfn, hR.zf, hnext.symm, hQN, hinvN _⟩⟩
            unfold evalInstrPMemF
            simp only [h1, h2, h3]
            rw [ite_eq_right (fun h => hz (hR.zf.symm.trans h))]
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
        refine ⟨1, { s' with prog := q' }, hone ?_, ⟨hfq, hR.zf, hpq, hQq, hiq _⟩⟩
        rw [hev, ite_eq_left (show gfn = (singletonProgM fn (expI e body 0)).lfn from hf), hq']; rfl
      · exact absurd hq (by simp)

/-- **A step of the body on the x86 flag machine is matched by the steps of its expansion.** -/
theorem expI_step {fn : String} {body : List LinstrRM} (h : ExpInv Q G Inv e body)
    {s s' u : LstateMF} (hR : RelI Q Inv e body s s')
    (hs : x86Isa.lsemStepPMemF (singletonProgM fn body) s = some u) :
    ∃ k u', Steps x86Isa (singletonProgM fn (expI e body 0)) k s' u'
      ∧ RelI Q Inv e body u u' := by
  unfold Isa.lsemStepPMemF at hs
  cases hf : findInstrMem (singletonProgM fn body) s.prog with
  | none => rw [hf] at hs; cases hs
  | some i =>
      rw [hf] at hs
      have hfn : s.prog.lfn = fn := by
        unfold findInstrMem at hf
        by_contra hc
        rw [ite_eq_right (show ¬ s.prog.lfn = (singletonProgM fn body).lfn from hc)] at hf
        cases hf
      have hget : body[s.prog.base.lpc]? = some i := by
        rw [findInstrMem_singleton fn body s.prog hfn] at hf
        exact hf
      exact evalInstrPMemF_expI_steps h hR hfn hget (fun _ _ _ _ => rfl) hs

/-- **A call tree related to the states of the body is related to the states of the
    expansion.** Under `ExpInv`, let every shadow instruction of a call of the body expand to
    itself, and at it the invariant and the relation give equal argument words at every choice
    of array positions and be kept by the write of every result. A tree related by `TSim` on
    the x86 flag machine to `s` at the call sites and the states after the calls of the body is
    related to every state `s'` that `RelI` relates to `s`, at the call sites and the states
    after the calls of the expansion, at every end condition that `RelI` carries `Post` to. -/
theorem tsim_expI {fn : String} {body : List LinstrRM} (h : ExpInv Q G Inv e body)
    (hcall : ∀ k i, body[k]? = some i → shadowCall? i.1 ≠ none →
      e k i = [i] ∧ ∀ (dst f : String) (srcs : List LOperand), i.1 = callShadow dst f srcs →
        ∀ (s s' : LstateMF) (x : CallRes), Inv k s.prog.base s.zf →
          Q s.prog.base s'.prog.base →
          (∀ a, argsRead a s'.prog.base 0 srcs = argsRead a s.prog.base 0 srcs)
            ∧ Inv (k + 1) (retRes dst x s).prog.base s.zf
            ∧ Q (retRes dst x s).prog.base (retRes dst x s').prog.base)
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', RelI Q Inv e body m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : RelI Q Inv e body s s')
    (hT : TSim x86Isa (singletonProgM fn body)
      (NFProgCallTreeExport.CallSite (singletonProgM fn body))
      (CallRet (singletonProgM fn body)) t s Post) :
    TSim x86Isa (singletonProgM fn (expI e body 0))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (expI e body 0)))
      (CallRet (singletonProgM fn (expI e body 0))) t s' Post' := by
  have hsh : ∀ (dst f : String) (srcs : List LOperand) (tag : MemTag),
      shadowCall? (callShadow dst f srcs, tag).1 ≠ none := fun dst f srcs tag => by
    simp only [LprogIsa.shadowCall?_callShadow]
    exact nofun
  have hfetchE : ∀ {k : Nat} {i : LinstrRM}, body[k]? = some i → e k i = [i] →
      (expI e body 0)[pcI e body k]? = some i := fun {k i} hb hself => by
    have := getElem?_expI_pcI e hb (j := 0) (by rw [hself]; simp)
    rw [Nat.add_zero, hself] at this
    simpa using this
  refine TSim.transfer (RelI Q Inv e body) (steps_sim_of_step _ fun s u s' hs hR =>
    expI_step h hR hs) ?_ ?_ hpost hR hT
  · rintro ev u u' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
    have hb : body[k]? = some (callShadow dst ev.name srcs, tag) := hfk
    obtain ⟨hself, hfacts⟩ := hcall k _ hb (hsh dst ev.name srcs tag)
    have hinv : Inv k u.prog.base u.zf := hat.2 ▸ hR.inv
    obtain ⟨hargs, -, -⟩ := hfacts dst ev.name srcs rfl u u' (.word 0) hinv hR.base
    refine ⟨dst, srcs, tag, pcI e body k, ⟨hR.lfn.trans hat.1, by rw [hR.pc, hat.2]⟩,
      hfetchE hb hself, hlen, ?_⟩
    rw [hargs]
    exact hrd
  · rintro ev u u' a v' hR ⟨dst, srcs, tag, k, hat, hfk, hlen, hrd⟩
      ⟨dst', srcs', tag', k', res, hat', hf', rfl, hout⟩
    have hb : body[k]? = some (callShadow dst ev.name srcs, tag) := hfk
    obtain ⟨hself, hfacts⟩ := hcall k _ hb (hsh dst ev.name srcs tag)
    have hk' : k' = pcI e body k := by rw [← hat'.2, hR.pc, hat.2]
    subst hk'
    have hf'' : (expI e body 0)[pcI e body k]? = some (callShadow dst' ev.name srcs', tag') := hf'
    rw [hfetchE hb hself] at hf''
    simp only [Option.some.injEq, Prod.mk.injEq, callShadow, LinstrR.Lopn.injEq,
      List.cons.injEq, LOperand.reg.injEq, and_true] at hf''
    obtain ⟨⟨rfl, -⟩, -⟩ := hf''
    obtain ⟨rfl, -, hback⟩ := callOut_retRes hout
    have hinv : Inv k u.prog.base u.zf := hat.2 ▸ hR.inv
    obtain ⟨-, hinv', hQ'⟩ := hfacts dst ev.name srcs rfl u u' (callResOf ev.resTys res) hinv
      hR.base
    refine ⟨retRes dst (callResOf ev.resTys res) u,
      ⟨dst, srcs, tag, k, res, hat, hfk, rfl, hback dst u⟩, ⟨?_, ?_, ?_, hQ', ?_⟩⟩
    · rw [lfn_retRes, lfn_retRes]
      exact hR.lfn
    · cases callResOf ev.resTys res <;> exact hR.zf
    · rw [lpc_retRes, lpc_retRes, hR.pc, hat.2, pcI_succ e hb, hself]
      rfl
    · rw [lpc_retRes, hat.2]
      cases hx : callResOf ev.resTys res <;> rw [hx] at hinv' <;> exact hinv'

/-- **A call tree carried through the fusion of the high multiplies.** For a body that passes
    `fuseOKL` and no fused position of which holds a call, a tree related by `TSim` on the x86
    flag machine to `s` at the call sites and the states after the calls of the body is related
    to every state `s'` that `RelI Agree (FInv E c)` relates to `s`, at the call sites and the
    states after the calls of the fused body, at every end condition that this relation carries
    `Post` to. -/
theorem tsim_fuse {E : List String} {L : List (Option String)} {c : List LinstrRM}
    (hok : fuseOKL E L c = true)
    (hL : ∀ (k : Nat) (i : LinstrRM) (d : String), c[k]? = some i → L[k]? = some (some d) →
      shadowCall? i.1 = none) {fn : String}
    {α : Type} {Post Post' : α → LstateMF → Prop}
    (hpost : ∀ x m m', RelI Agree (FInv E c) (fuseE L) c m m' → Post x m → Post' x m')
    {t : CallTree (nfCallSig jasminDialect) (Option α)} {s s' : LstateMF}
    (hR : RelI Agree (FInv E c) (fuseE L) c s s')
    (hT : TSim x86Isa (singletonProgM fn c) (NFProgCallTreeExport.CallSite (singletonProgM fn c))
      (CallRet (singletonProgM fn c)) t s Post) :
    TSim x86Isa (singletonProgM fn (expI (fuseE L) c 0))
      (NFProgCallTreeExport.CallSite (singletonProgM fn (expI (fuseE L) c 0)))
      (CallRet (singletonProgM fn (expI (fuseE L) c 0))) t s' Post' :=
  tsim_expI (expInv_fuse hok)
    (fun _ _ hk hsh => ⟨fuseE_call hL hk hsh, fun _ _ _ hi _ _ x hI hA =>
      ⟨fun a => (fuse_call hok hk hi a x hI hA).1,
        (fuse_call hok hk hi (fun _ => none) x hI hA).2⟩⟩)
    hpost hR hT

end Sim

end CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExpand
