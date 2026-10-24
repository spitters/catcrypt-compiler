/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module
public import CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
public import CatCrypt.Crypto.SecureCompilation.X86Backend.CalleeSig

/-!
# The byte check with a call of a linked callee

A caller program `p` is linked to the bytes of a callee `q` as `p ++ shiftProg p.length q`,
and every `call` of `p` targets the index `p.length`. The check `checkCertX` assigns a
public set to the indices of `p` (a certificate) and checks the caller's segments between
calls as `DecodedCT.checkCert` does. Its call arm checks the stack operations of the call
(`blockOkA` on `callOps`), that the public set after them covers `%rsp` and the registers
`pubRegs` (`callPub`), the stack operation of the return from a state where only `%rsp`
is public, and that the public set after the return is below the part of the caller's set
that the callee keeps (`DecodedCT.keepA`).

The callee is the leaky run of `q`, guarded by the precondition of its interface
(`guarded`): an answer of the oracle is a run of `q` from an entry state that satisfies
the precondition. Two runs of `p` that halt under this oracle from states agreeing on the
certificate's set at index `0` have equal traces as runs of the linked program.

## Main results

* `callPub`, `checkAtX`, `checkCertX`: the check with an external call arm.
* `segRun_certX_sound`: two segments of a checked caller from states agreeing on the
  certificate have equal traces and stop at related ends.
* `presPost_of_calleeSpec`: a specified callee whose footprint lies in the `G` bytes below
  its entry stack register preserves the registers outside its clobber set and the frame
  words above its entry stack register.
* `presPostO_of_calleeSpec`: the same for a callee whose footprint also covers an out region
  `O`, for frame words outside `O`.
* `OracleRun.mono_oracle`: a run under an oracle is a run under every oracle with more
  answers.
* `linkedRunX_trace_eq`: equal traces of the linked program for two runs of a checked
  caller that halt under the guarded oracle of the callee.
* `linkedRunX_trace_eq_out`: the same for a callee with an out region `O`, when the frame
  words the caller keeps lie outside `O`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.MachineConstantTime
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCT
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink
open CatCrypt.Crypto.SecureCompilation.X86Backend.Callee
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.CT
open CatCrypt.Crypto.SecureCompilation.X86Backend.DecodePrintedAddrLeak (runL_det)

/-! ## 1. The check -/

/-- The public set the stack operations of a call must leave: `%rsp` and the registers
    `pubRegs`. -/
def callPub (pubRegs : List String) : PubA := ⟨"%rsp" :: pubRegs, [], false, []⟩

/-- The public set of the stack register alone. -/
def rspPub : PubA := ⟨["%rsp"], [], false, []⟩

/-- Under the regime `doitm` the stack operation of a return passes the block check from
    `rspPub`. -/
theorem blockOkA_rspPub_retOps_doitm (F : List Int) : blockOkA .doitm F rspPub retOps = true :=
  rfl

/-- The check at index `pc` of a caller whose calls target the external entry `ext`. The
    arms other than `call` are those of `DecodedCT.checkAt` without owners; a `ret` ends a
    segment and is not checked. A `call t` needs `t = ext`, the block check of `callOps`,
    the public set `callPub pubRegs` below the set after `callOps`, the block check of
    `retOps` from `rspPub`, and the successor below `keepA R Q a`. -/
def checkAtX (r : DoitRegime) (F : List Int) (ext : Nat) (pubRegs R : List String)
    (Q : List Int) (prog : List RInstr) (A : List (Option PubA)) (pc : Nat) : Bool :=
  match certAt A pc with
  | none => true
  | some a => a.cells.all F.contains &&
    match prog[pc]? with
    | some (.op i) => opOk r a i && succOk A (pc + 1) (stepA a i)
    | some (.jcc cc t) =>
        a.flags && (condtOfNibble cc).isSome && succOk A t a && succOk A (pc + 1) a
    | some (.push x) =>
        blockOkA r F a (pushOps x) && succOk A (pc + 1) (stepBlock a (pushOps x))
    | some (.pop x) =>
        blockOkA r F a (popOps x) && succOk A (pc + 1) (stepBlock a (popOps x))
    | some .ret => true
    | some (.call t) =>
        t == ext && blockOkA r F a (callOps (pc + 1))
          && (callPub pubRegs).le (stepBlock a (callOps (pc + 1)))
          && blockOkA r F rspPub retOps
          && succOk A (pc + 1) (keepA R Q a)
    | none => true

/-- The check at every index of `prog`. -/
def checkCertX (r : DoitRegime) (F : List Int) (ext : Nat) (pubRegs R : List String)
    (Q : List Int) (prog : List RInstr) (A : List (Option PubA)) : Bool :=
  (List.range prog.length).all (checkAtX r F ext pubRegs R Q prog A)

theorem checkAtX_of_checkCertX {r : DoitRegime} {F : List Int} {ext : Nat}
    {pubRegs R : List String} {Q : List Int} {prog : List RInstr} {A : List (Option PubA)}
    (hc : checkCertX r F ext pubRegs R Q prog A = true) {pc : Nat} {x : RInstr}
    (hx : prog[pc]? = some x) : checkAtX r F ext pubRegs R Q prog A pc = true := by
  have hlt : pc < prog.length := (List.getElem?_eq_some_iff.mp hx).1
  exact List.all_eq_true.mp hc pc (List.mem_range.mpr hlt)

/-- Two states agree on the public set the certificate assigns to `pc`. -/
def CertRel (A : List (Option PubA)) (pc : Nat) (s₁ s₂ : AState) : Prop :=
  ∃ a, certAt A pc = some a ∧ a.Agree s₁ s₂

/-- Two states at the call site `pc` of a call to `tgt` agree on the certificate's set. -/
def SiteRel (prog : List RInstr) (A : List (Option PubA)) (pc tgt : Nat) (s₁ s₂ : AState) :
    Prop :=
  prog[pc]? = some (.call tgt) ∧ CertRel A pc s₁ s₂

/-! ## 2. Soundness on segments -/

/-- **Soundness of the check on segments.** Two segments of a program that passes
    `checkCertX`, whose steps satisfy `FrameSep F`, from states agreeing on the set the
    certificate assigns to `pc`, have equal traces and stop at related ends: both at a
    `ret`, or both at the same call site in states agreeing on the certificate. -/
theorem segRun_certX_sound {r : DoitRegime} {F : List Int} {ext : Nat}
    {pubRegs R : List String} {Q : List Int} {prog : List RInstr} {A : List (Option PubA)}
    (hc : checkCertX r F ext pubRegs R Q prog A = true) {pc : Nat} {s₁ : AState}
    {t₁ : List CTLeak} {e₁ : SegEnd} (h₁ : SegRun r (FrameSep F) prog pc s₁ t₁ e₁) :
    ∀ {a : PubA} {s₂ : AState} {t₂ : List CTLeak} {e₂ : SegEnd}, certAt A pc = some a →
      a.Agree s₁ s₂ → SegRun r (FrameSep F) prog pc s₂ t₂ e₂ →
        t₁ = t₂ ∧ SegEnd.Rel (SiteRel prog A) e₁ e₂ := by
  induction h₁ with
  | @ret pc s₁ h =>
    intro a s₂ t₂ e₂ hA hag h₂
    cases h₂ with
    | ret => exact ⟨rfl, trivial⟩
    | site h' => simp_all
    | op h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
  | @site pc tgt s₁ h =>
    intro a s₂ t₂ e₂ hA hag h₂
    cases h₂ with
    | ret h' => simp_all
    | @site _ tgt' _ h' =>
      rw [h, Option.some.injEq, RInstr.call.injEq] at h'
      subst h'
      exact ⟨rfl, rfl, rfl, h, a, hA, hag⟩
    | op h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
  | @op pc s₁ i t₁ e₁ h hok hr ih =>
    intro a s₂ t₂ e₂ hA hag h₂
    have hck := checkAtX_of_checkCertX hc h
    simp only [checkAtX, hA, h, Bool.and_eq_true] at hck
    obtain ⟨hF, hop, hsucc⟩ := hck
    have hF : ∀ o ∈ a.cells, o ∈ F := fun o ho => by
      simpa using List.all_eq_true.mp hF o ho
    obtain ⟨b, hb, hle⟩ := succOk_spec hsucc
    cases h₂ with
    | ret h' => simp_all
    | site h' => simp_all
    | jcc h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | @op _ _ i' t₂ _ h' hok' hr' =>
      rw [h, Option.some.injEq, RInstr.op.injEq] at h'
      subst h'
      obtain ⟨ht, hs⟩ :=
        ih hb (PubA.agree_of_le hle (stepA_sound a i (fun _ => hF) hag hok hok')) hr'
      exact ⟨by rw [opLeak_eq hop hag, ht], hs⟩
  | @jcc pc s₁ cc tgt c t₁ e₁ h hcc hr ih =>
    intro a s₂ t₂ e₂ hA hag h₂
    have hck := checkAtX_of_checkCertX hc h
    simp only [checkAtX, hA, h, Bool.and_eq_true] at hck
    obtain ⟨_, ⟨⟨⟨hfl, _⟩, hst⟩, hsn⟩⟩ := hck
    cases h₂ with
    | ret h' => simp_all
    | site h' => simp_all
    | op h' => simp_all
    | stack h' hops' => simp_all [RInstr.stackOps?]
    | @jcc _ _ cc' tgt' c' t₂ _ h' hcc' hr' =>
      rw [h, Option.some.injEq, RInstr.jcc.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rw [hcc, Option.some.injEq] at hcc'
      subst hcc'
      have hcb := condB_eq (hag.2.2.1 hfl) c
      by_cases hcnd : s₂.view.condB c = true
      · obtain ⟨b, hb, hle⟩ := succOk_spec hst
        simp only [hcb, hcnd, ite_true] at ih hr'
        obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag) hr'
        exact ⟨by rw [hcb, ht], hs⟩
      · obtain ⟨b, hb, hle⟩ := succOk_spec hsn
        simp only [hcb, hcnd, ite_false, Bool.false_eq_true] at ih hr'
        obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag) hr'
        exact ⟨by rw [hcb, ht], hs⟩
  | @stack pc s₁ ri ops t₁ e₁ h hops hok hr ih =>
    intro a s₂ t₂ e₂ hA hag h₂
    have hck := checkAtX_of_checkCertX hc h
    have key : blockOkA r F a ops = true ∧ succOk A (pc + 1) (stepBlock a ops) = true := by
      cases ri <;> simp only [RInstr.stackOps?, reduceCtorEq, Option.some.injEq] at hops <;>
        subst hops <;> simp only [checkAtX, hA, h, Bool.and_eq_true] at hck <;>
        exact hck.2
    obtain ⟨hbk, hsucc⟩ := key
    obtain ⟨b, hb, hle⟩ := succOk_spec hsucc
    cases h₂ with
    | ret h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | site h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | op h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | jcc h' =>
      rw [h, Option.some.injEq] at h'; subst h'; simp [RInstr.stackOps?] at hops
    | @stack _ _ ri' ops' t₂ _ h' hops' hok' hr' =>
      rw [h, Option.some.injEq] at h'
      subst h'
      rw [hops, Option.some.injEq] at hops'
      subst hops'
      obtain ⟨hl, hag'⟩ := blockOkA_sound ops a hbk hag hok hok'
      obtain ⟨ht, hs⟩ := ih hb (PubA.agree_of_le hle hag') hr'
      exact ⟨by rw [hl, ht], hs⟩

/-! ## 3. What a specified callee preserves -/

/-- The stack operations of a call satisfy `FrameSep`: the store goes through `%rsp`. -/
theorem blockOk_frameSep_callOps (F : List Int) (s : AState) (n : Nat) :
    BlockOk (FrameSep F) s (callOps n) := by
  simp [BlockOk, FrameSep, callOps, frameWrite, writeAddr]

/-- The stack operation of a return satisfies `FrameSep`: it writes no memory. -/
theorem blockOk_frameSep_retOps (F : List Int) (s : AState) :
    BlockOk (FrameSep F) s retOps := by
  simp [BlockOk, FrameSep, retOps, frameWrite, writeAddr]

/-- A word at a non-negative offset `q` above `e` with `q + 8 + G ≤ 2 ^ 64` lies outside
    the `G` bytes below `e`. -/
theorem not_inFrame_of_inRange8 {e x : BitVec 64} {G : Nat} {q : Int} (h0 : 0 ≤ q)
    (hq : q + 8 + G ≤ 2 ^ 64) (hx : InRange8 (e + BitVec.ofInt 64 q) x) :
    ¬ InFrame e G x := by
  intro hf
  unfold InRange8 at hx
  unfold InFrame at hf
  have he := e.isLt
  have hx' := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofInt] at hx hf
  omega

/-- **What a specified callee with an out region preserves.** Let the footprint of `c` lie
    in the `G` bytes below the entry stack register or in the out region `O` of the entry
    state, the registers `R` lie outside the clobber set, and the offsets `Q` be
    non-negative with `q + 8 + G ≤ 2 ^ 64` and their words outside `O`. A run of a callee
    with `CalleeSpec X c` from an entry state satisfying the precondition restores `%rsp`
    and keeps the registers `R` and the frame words at the offsets `Q`. -/
theorem presPostO_of_calleeSpec {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {R : List String} {Q : List Int} {G : Nat} {O : AState → BitVec 64 → Prop}
    (hR : ∀ x ∈ R, c.clob x = false)
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x ∨ O s x)
    (hQ : ∀ q ∈ Q, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64)
    (hQO : ∀ s, ∀ q ∈ Q, ∀ x, InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x → ¬ O s x)
    {s s' : AState} {t : List CTLeak} (hpre : c.pre s) (hrun : X s t s') :
    PresPost R Q s s' := by
  have hrsp := hX.rsp _ _ _ hpre hrun
  refine ⟨hrsp, fun x hx => hX.keep _ _ _ hpre hrun x (hR x hx), fun q hq => ?_⟩
  obtain ⟨h0, hq8⟩ := hQ q hq
  unfold cellAt
  rw [hrsp]
  have hm : ∀ x, InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x → s'.mem x = s.mem x :=
    fun x hx => hX.frame _ _ _ hpre hrun x fun hf =>
      (hfoot s x hf).elim (not_inFrame_of_inRange8 h0 hq8 hx) (hQO s q hq x hx)
  set a := s.regs "%rsp" + BitVec.ofInt 64 q
  have hk : ∀ k, k < 8 → s'.mem (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) :=
    fun k hk => hm _ (by unfold InRange8; simp; omega)
  have h0' : s'.mem a = s.mem a := by simpa using hk 0 (by decide)
  simp only [read64, h0', hk 1 (by decide), hk 2 (by decide), hk 3 (by decide),
    hk 4 (by decide), hk 5 (by decide), hk 6 (by decide), hk 7 (by decide)]

/-- **What a specified callee preserves.** Let the footprint of `c` lie in the `G` bytes
    below the entry stack register, the registers `R` lie outside the clobber set and the
    offsets `Q` be non-negative with `q + 8 + G ≤ 2 ^ 64`. A run of a callee with
    `CalleeSpec X c` from an entry state satisfying the precondition restores `%rsp` and
    keeps the registers `R` and the frame words at the offsets `Q`. -/
theorem presPost_of_calleeSpec {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {R : List String} {Q : List Int} {G : Nat} (hR : ∀ x ∈ R, c.clob x = false)
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x)
    (hQ : ∀ q ∈ Q, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64) {s s' : AState} {t : List CTLeak}
    (hpre : c.pre s) (hrun : X s t s') : PresPost R Q s s' :=
  presPostO_of_calleeSpec (O := fun _ _ => False) hX hR (fun s x h => Or.inl (hfoot s x h)) hQ
    (fun _ _ _ _ _ h => h) hpre hrun

/-! ## 4. Runs under the guarded oracle -/

/-- A run with leakage under an oracle is a run under every oracle with more answers. -/
theorem _root_.CatCrypt.Crypto.SecureCompilation.X86Backend.Callee.OracleRun.mono_oracle {r : DoitRegime} {ok : AState → JInstr 64 → Prop}
    {O O' : Nat → CalleeRun} (hO : ∀ tg s tr sc, O tg s tr sc → O' tg s tr sc)
    {prog : List RInstr} {pc : Nat} {sa : AState} {t : List CTLeak} {sa' : AState}
    (h : OracleRun r ok O prog pc sa t sa') : OracleRun r ok O' prog pc sa t sa' := by
  induction h with
  | ret h => exact .ret h
  | op h hok _ ih => exact .op h hok ih
  | jcc h hc _ ih => exact .jcc h hc ih
  | stack h hops hok _ ih => exact .stack h hops hok ih
  | call h hok hc hokr _ ih => exact .call h hok (hO _ _ _ _ hc) hokr ih

/-- The callee `X` guarded by the precondition of `c`: its runs from entry states that
    satisfy `c.pre`. -/
def guarded (c : CalleeSig) (X : CalleeRun) : CalleeRun :=
  fun s t s' => c.pre s ∧ X s t s'

/-- The interface of the guarded callee seen by the caller's check: no precondition, and
    entry states related when they agree on `callPub pubRegs`. -/
def guardedSig (c : CalleeSig) (pubRegs : List String) : CalleeSig :=
  { c with pre := fun _ => True, pub := (callPub pubRegs).Agree }

/-- The guarded callee has the leakage summary of `guardedSig`, with the trivial exit
    relation, when agreement on `callPub pubRegs` between entry states that satisfy the
    precondition gives `c.pub`. -/
theorem pubSummary_guarded {X : CalleeRun} {c : CalleeSig} (hX : CalleeSpec X c)
    {pubRegs : List String}
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂) :
    PubSummary (guarded c X) (guardedSig c pubRegs) (fun _ _ => True) :=
  ⟨fun _ _ _ _ _ _ _ _ hp hX₁ hX₂ =>
      hX.ct _ _ _ _ _ _ hX₁.1 hX₂.1 (hpub _ _ hX₁.1 hX₂.1 hp) hX₁.2 hX₂.2,
    fun _ _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-- **Equal leakage of the linked program under the guarded oracle of a callee with an out
    region.** Let `q` be a block without `call` with `CalleeSpec (runOf r q) c`, whose
    footprint lies in the `G` bytes below the entry stack register or in the out region
    `O` of the entry state, and let the caller `p` pass `checkCertX` at the entry
    `p.length` with registers `R` outside the clobber set, offsets `Q` as in
    `presPostO_of_calleeSpec`, and agreement on `callPub pubRegs` giving `c.pub`. Let `p`
    halt under the oracle of the guarded callee from two states agreeing on the
    certificate's set at index `0`, with the runs under the oracle satisfying `FrameSep F`.
    Then every two runs with leakage of `p ++ shiftProg p.length q` from these states have
    equal traces. -/
theorem linkedRunX_trace_eq_out {r : DoitRegime} {F : List Int} {pubRegs R : List String}
    {Q : List Int} {A : List (Option PubA)} {p q : List RInstr}
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf r q) c)
    (hc : checkCertX r F p.length pubRegs R Q p A = true)
    (hR : ∀ x ∈ R, c.clob x = false) {G : Nat} {O : AState → BitVec 64 → Prop}
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x ∨ O s x)
    (hQ : ∀ q ∈ Q, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64)
    (hQO : ∀ s, ∀ q ∈ Q, ∀ x, InRange8 (s.regs "%rsp" + BitVec.ofInt 64 q) x → ¬ O s x)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hI : CertRel A 0 s₁ s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf r q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf r q))) p 0 s₂ s₂')
    (hsep₁ : ∀ t s', OracleRun r (fun _ _ => True) (tracedAt p.length (guarded c (runOf r q)))
      p 0 s₁ t s' →
      OracleRun r (FrameSep F) (tracedAt p.length (guarded c (runOf r q))) p 0 s₁ t s')
    (hsep₂ : ∀ t s', OracleRun r (fun _ _ => True) (tracedAt p.length (guarded c (runOf r q)))
      p 0 s₂ t s' →
      OracleRun r (FrameSep F) (tracedAt p.length (guarded c (runOf r q))) p 0 s₂ t s')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL r ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL r ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ := by
  have hdrop : ∀ tg s tr sc, tracedAt p.length (guarded c (runOf r q)) tg s tr sc →
      tracedAt p.length (fun s t s' => RunL r (fun _ _ => True) q 0 s t s') tg s tr sc :=
    fun _ _ _ _ ho => ⟨ho.1, ho.2.2⟩
  obtain ⟨u₁, ho₁⟩ := oracleRun_of_haltsO_oracleAt r h₁
  obtain ⟨u₂, ho₂⟩ := oracleRun_of_haltsO_oracleAt r h₂
  obtain ⟨rfl, _⟩ := runL_det (runL_append_of_oracleRun p q hq (ho₁.mono_oracle hdrop)) hr₁
  obtain ⟨rfl, _⟩ := runL_det (runL_append_of_oracleRun p q hq (ho₂.mono_oracle hdrop)) hr₂
  refine oracleRun_trace_eq (pubSummary_guarded hX hpub) (I := CertRel A) (E := SiteRel p A)
    (fun pc s₁ s₂ t₁ t₂ e₁ e₂ ⟨a, hA, hag⟩ hs₁ hs₂ => segRun_certX_sound hc hs₁ hA hag hs₂)
    (fun pc tg a b ⟨hcall, x, hA, hag⟩ => ?_)
    (fun pc tg a b t₁ t₂ sc₁ sc₂ ⟨hcall, x, hA, hag⟩ hX₁ hX₂ _ => ?_)
    hI (hsep₁ _ _ ho₁) (hsep₂ _ _ ho₂)
  · have hck := checkAtX_of_checkCertX hc hcall
    simp only [checkAtX, hA, hcall, Bool.and_eq_true] at hck
    obtain ⟨_, ⟨⟨⟨_, hbk⟩, hle⟩, _⟩, _⟩ := hck
    obtain ⟨hl, hag'⟩ := blockOkA_sound _ x hbk hag (blockOk_frameSep_callOps F a (pc + 1))
      (blockOk_frameSep_callOps F b (pc + 1))
    exact ⟨trivial, trivial, PubA.agree_of_le hle hag', hl⟩
  · have hck := checkAtX_of_checkCertX hc hcall
    simp only [checkAtX, hA, hcall, Bool.and_eq_true] at hck
    obtain ⟨_, ⟨⟨⟨_, hbk⟩, hle⟩, hbr⟩, hsucc⟩ := hck
    obtain ⟨_, hag'⟩ := blockOkA_sound _ x hbk hag (blockOk_frameSep_callOps F a (pc + 1))
      (blockOk_frameSep_callOps F b (pc + 1))
    have hpk := PubA.agree_of_le hle hag'
    have hrsp : sc₁.regs "%rsp" = sc₂.regs "%rsp" := by
      rw [hX.rsp _ _ _ hX₁.1 hX₁.2, hX.rsp _ _ _ hX₂.1 hX₂.2]
      exact hpk.1 "%rsp" (by simp [callPub])
    have hra : rspPub.Agree sc₁ sc₂ :=
      ⟨fun y hy => by simp only [rspPub, List.mem_singleton] at hy; subst hy; exact hrsp,
        fun o ho => by simp [rspPub] at ho, fun hf => by simp [rspPub] at hf,
        fun q hq => by simp [rspPub] at hq⟩
    obtain ⟨hl, _⟩ := blockOkA_sound _ _ hbr hra (blockOk_frameSep_retOps F sc₁)
      (blockOk_frameSep_retOps F sc₂)
    have hkeep := keepA_agree hag (presPostO_of_calleeSpec hX hR hfoot hQ hQO hX₁.1 hX₁.2)
      (presPostO_of_calleeSpec hX hR hfoot hQ hQO hX₂.1 hX₂.2)
    obtain ⟨b', hb', hle'⟩ := succOk_spec hsucc
    exact ⟨hl, b', hb', PubA.agree_of_le hle' hkeep⟩

/-- **Equal leakage of the linked program under the guarded oracle.** Let `q` be a block
    without `call` with `CalleeSpec (runOf r q) c`, whose footprint lies in the `G` bytes
    below the entry stack register, and let the caller `p` pass `checkCertX` at the entry
    `p.length` with registers `R` outside the clobber set, offsets `Q` as in
    `presPost_of_calleeSpec`, and agreement on `callPub pubRegs` giving `c.pub`. Let `p`
    halt under the oracle of the guarded callee from two states agreeing on the
    certificate's set at index `0`, with the runs under the oracle satisfying `FrameSep F`.
    Then every two runs with leakage of `p ++ shiftProg p.length q` from these states have
    equal traces. -/
theorem linkedRunX_trace_eq {r : DoitRegime} {F : List Int} {pubRegs R : List String}
    {Q : List Int} {A : List (Option PubA)} {p q : List RInstr}
    (hq : ∀ tg, RInstr.call tg ∉ q) {c : CalleeSig} (hX : CalleeSpec (runOf r q) c)
    (hc : checkCertX r F p.length pubRegs R Q p A = true)
    (hR : ∀ x ∈ R, c.clob x = false) {G : Nat}
    (hfoot : ∀ s x, c.foot s x → InFrame (s.regs "%rsp") G x)
    (hQ : ∀ q ∈ Q, 0 ≤ q ∧ q + 8 + G ≤ 2 ^ 64)
    (hpub : ∀ s₁ s₂, c.pre s₁ → c.pre s₂ → (callPub pubRegs).Agree s₁ s₂ → c.pub s₁ s₂)
    {s₁ s₂ s₁' s₂' : AState} (hI : CertRel A 0 s₁ s₂)
    (h₁ : HaltsO aMachine (oracleAt p.length (guarded c (runOf r q))) p 0 s₁ s₁')
    (h₂ : HaltsO aMachine (oracleAt p.length (guarded c (runOf r q))) p 0 s₂ s₂')
    (hsep₁ : ∀ t s', OracleRun r (fun _ _ => True) (tracedAt p.length (guarded c (runOf r q)))
      p 0 s₁ t s' →
      OracleRun r (FrameSep F) (tracedAt p.length (guarded c (runOf r q))) p 0 s₁ t s')
    (hsep₂ : ∀ t s', OracleRun r (fun _ _ => True) (tracedAt p.length (guarded c (runOf r q)))
      p 0 s₂ t s' →
      OracleRun r (FrameSep F) (tracedAt p.length (guarded c (runOf r q))) p 0 s₂ t s')
    {ok₁ ok₂ : AState → JInstr 64 → Prop} {t₁ t₂ : List CTLeak} {e₁ e₂ : AState}
    (hr₁ : RunL r ok₁ (p ++ shiftProg p.length q) 0 s₁ t₁ e₁)
    (hr₂ : RunL r ok₂ (p ++ shiftProg p.length q) 0 s₂ t₂ e₂) : t₁ = t₂ :=
  linkedRunX_trace_eq_out (O := fun _ _ => False) hq hX hc hR
    (fun s x h => Or.inl (hfoot s x h)) hQ (fun _ _ _ _ _ h => h) hpub hI h₁ h₂ hsep₁ hsep₂
    hr₁ hr₂

end CatCrypt.Crypto.SecureCompilation.X86Backend.DecodedCTCall
