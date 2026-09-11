/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JasminSem
public import CatCrypt.Crypto.CompilerSecurity.UnifiedTrace


@[expose] public section
set_option autoImplicit false

/-!
# JasminSemTraced: trace-emitting big-step semantics (Track A1.5)

The existing `jasminSem` (in `CatCrypt/Crypto/Jasmin/JasminSem.lean`) is a
Prop relation `Cmd → RustState → RustState → Prop`; it carries no trace.
This file adds a parallel inductive `jasminSemTraced` whose derivations
also produce a `LeakTrace`. Each existing `jasminSem` rule has a
trace-emitting counterpart with the same premises plus a trace
contribution; sequential composition concatenates traces.

Branch decisions in `Cif` are encoded as distinct trace events
(`pureOp "branch:true"` / `pureOp "branch:false"`) on top of the
`pureOp "Cif"` for the instruction itself. This is the dynamic
information that the structural `JasminSem.Cmd.leakTrace` cannot see.

## Forgetting

`jasminSemTraced` is *strictly more informative* than `jasminSem`:
forgetting the trace recovers the latter. We prove
`jasminSemTraced.toSem` for the forgetting direction. The converse
(every `jasminSem` derivation can be promoted to a `jasminSemTraced`
derivation by recording the dynamic events) holds at the meta-level
since every `jasminSem` rule has a `jasminSemTraced` counterpart, but
formal proof requires re-doing the `induction h with` over `jasminSem`.
We provide that promotion as `jasminSem.toTraced`.

## Use case

For RHP-2 over programs with control flow: a target adversary observes
the dynamic trace (including branch decisions). To back-translate it
to the source side, we need the source-side counterpart, which means
extending `RustExec` with the same dynamic branch events. That is the
final piece (A1.11) noted in `next.md` Tier 3 #14.
-/

namespace CatCrypt.Crypto.SecureCompilation.JasminSemTraced

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.Jasmin.SemBridge
open CatCrypt.Crypto.SecureCompilation.CryptoSSA

/-- Branch-decision tag for the dynamic if-trace. -/
def branchTag (taken : Bool) : LeakEvent :=
  LeakEvent.pureOp (if taken then "branch:true" else "branch:false")

/-- Trace-emitting big-step semantics. Each rule mirrors one of
    `jasminSem`'s with the trace contribution added. -/
inductive jasminSemTraced (leafSpec : LeafSpec) :
    Cmd → RustState → LeakTrace → RustState → Prop where
  | nil : ∀ rs, jasminSemTraced leafSpec [] rs [] rs
  | cons : ∀ i is rs t1 rs1 t2 rs',
      jasminSemTraced leafSpec [i] rs t1 rs1 →
      jasminSemTraced leafSpec is rs1 t2 rs' →
      jasminSemTraced leafSpec (i :: is) rs (t1 ++ t2) rs'
  | assgn_parr_init : ∀ x t rs,
      jasminSemTraced leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t.storageBytes },
                           info := { towerTag := t.byteSize } })
                 .AT_none (.sarr t.storageBytes) (.Parr_init t.storageBytes)]
        rs [LeakEvent.pureOp "Cassgn"] (rsSetTower rs x ⟨t, default⟩)
  | assgn_u64_zero : ∀ x rs,
      jasminSemTraced leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64) (.Pconst 0)]
        rs [LeakEvent.pureOp "Cassgn"] (rsSetScalar rs x 0)
  | assgn_u64_val : ∀ x (v : Nat) rs,
      jasminSemTraced leafSpec
        [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64)
                 (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
        rs [LeakEvent.pureOp "Cassgn"] (rsSetScalar rs x v)
  /-- `Cif` true branch — emits the `Cif` tag, then a `branch:true` tag,
      then the inner-branch trace. -/
  | if_true : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState) (v : Nat)
                (tInner : LeakTrace),
      rs.rsScalar e = v → v ≠ 0 →
      jasminSemTraced leafSpec ct rs tInner rs' →
      jasminSemTraced leafSpec
        [.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
        rs (LeakEvent.pureOp "Cif" :: branchTag true :: tInner) rs'
  /-- `Cif` false branch — analogous, with `branch:false`. -/
  | if_false : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState)
                  (tInner : LeakTrace),
      rs.rsScalar e = 0 →
      jasminSemTraced leafSpec cf rs tInner rs' →
      jasminSemTraced leafSpec
        [.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
        rs (LeakEvent.pureOp "Cif" :: branchTag false :: tInner) rs'
  | call_oracle : ∀ (f : String) (dest : Located) (args : List Located)
                    (rs : RustState) (oldDestV : RustVal dest.locDst)
                    (argList : List (Σ t, RustVal t)),
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Per-arg type-recovery (Option A): args[i].locDst matches the
      -- stored Sigma type at args[i].locVar. Required for determinism.
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      jasminSemTraced leafSpec
        [.Ccall .DoNotInline [locToLVal dest] { name := f } (args.map locToPExpr)]
        rs [LeakEvent.pureOp "Ccall"]
        (locatedUpdate rs dest
              (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | limb_store_oracle : ∀ (loc : Located) (idx : Nat) (v : BitVec 64)
                         (rs : RustState) (oldDestV : RustVal loc.locDst),
      locatedLookup rs loc = some oldDestV →
      jasminSemTraced leafSpec
        [.Copn [locToLVal loc] .AT_none (.Oasm { name := "STORE64" })
               [locToPExpr loc, .Pconst idx, .Pconst v.toNat]]
        rs [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  | clone_tower : ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
                    (rs : RustState),
      jasminSemTraced leafSpec
        [.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr cloneTy.storageBytes },
                         info := { towerTag := cloneTy.byteSize } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" }) [locToPExpr oldDest]]
        rs [LeakEvent.pureOp "Copn"]
        (rsSetTower rs cloneVar
             ((rs.rsTower oldDest.locVar).getD ⟨cloneTy, default⟩))

/-! ## Forgetting: `jasminSemTraced ⟹ jasminSem` -/

/-- Forgetting the trace: every `jasminSemTraced` derivation projects
    to a `jasminSem` derivation (modulo the recorded trace). -/
theorem jasminSemTraced.toSem (leafSpec : LeafSpec)
    {body : Cmd} {rs rs' : RustState} {t : LeakTrace}
    (h : jasminSemTraced leafSpec body rs t rs') :
    jasminSem leafSpec body rs rs' := by
  induction h with
  | nil rs0 => exact jasminSem.nil rs0
  | cons _ _ _ _ _ _ _ _ _ ih1 ih2 =>
    exact jasminSem.cons _ _ _ _ _ ih1 ih2
  | assgn_parr_init x t' rs0 => exact jasminSem.assgn_parr_init x t' rs0
  | assgn_u64_zero x rs0     => exact jasminSem.assgn_u64_zero x rs0
  | assgn_u64_val x v rs0    => exact jasminSem.assgn_u64_val x v rs0
  | if_true e ct cf rs0 rs0' v _ hv hne _ ih =>
    exact jasminSem.if_true e ct cf rs0 rs0' v hv hne ih
  | if_false e ct cf rs0 rs0' _ h0 _ ih =>
    exact jasminSem.if_false e ct cf rs0 rs0' h0 ih
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact jasminSem.call_oracle f dest args rs0 oldDestV argList hLk hArgs
            hArgsTyped
  | limb_store_oracle loc idx v rs0 oldDestV hLk =>
    exact jasminSem.limb_store_oracle loc idx v rs0 oldDestV hLk
  | clone_tower cv ct oldDest rs0 => exact jasminSem.clone_tower cv ct oldDest rs0

/-- Concatenation: traced executions compose with their traces appended.
    Mirror of `jasminSem_seq_compose` for the trace-emitting version. -/
theorem jasminSemTraced_seq_compose
    (leafSpec : LeafSpec) (l1 l2 : Cmd) (rs r1 rs' : RustState)
    (t1 t2 : LeakTrace)
    (h1 : jasminSemTraced leafSpec l1 rs t1 r1)
    (h2 : jasminSemTraced leafSpec l2 r1 t2 rs') :
    jasminSemTraced leafSpec (l1 ++ l2) rs (t1 ++ t2) rs' := by
  induction h1 generalizing l2 rs' t2 with
  | nil rs0 => simpa using h2
  | cons i is rs0 t1' rs1 t2' r1' _hi _his _ih1 ih2 =>
    -- Goal: jasminSemTraced ((i :: is) ++ l2) rs0 ((t1' ++ t2') ++ t2) rs'
    show jasminSemTraced leafSpec ((i :: is) ++ l2) rs0
            ((t1' ++ t2') ++ t2) rs'
    rw [List.append_assoc]
    exact jasminSemTraced.cons i (is ++ l2) rs0 t1' rs1 (t2' ++ t2) rs'
            _hi (ih2 l2 rs' t2 h2)
  | assgn_parr_init x t' rs0 =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.assgn_parr_init x t' rs0) h2
  | assgn_u64_zero x rs0 =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.assgn_u64_zero x rs0) h2
  | assgn_u64_val x v rs0 =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.assgn_u64_val x v rs0) h2
  | if_true e ct cf rs0 r1' v tInner hv hne hct =>
    exact jasminSemTraced.cons _ l2 rs0 _ r1' t2 rs'
            (jasminSemTraced.if_true e ct cf rs0 r1' v tInner hv hne hct) h2
  | if_false e ct cf rs0 r1' tInner h0 hcf =>
    exact jasminSemTraced.cons _ l2 rs0 _ r1' t2 rs'
            (jasminSemTraced.if_false e ct cf rs0 r1' tInner h0 hcf) h2
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.call_oracle f dest args rs0 oldDestV argList hLk hArgs
                                          hArgsTyped) h2
  | limb_store_oracle loc idx v rs0 oldDestV hLk =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.limb_store_oracle loc idx v rs0 oldDestV hLk) h2
  | clone_tower cv ct oldDest rs0 =>
    exact jasminSemTraced.cons _ l2 rs0 _ _ t2 rs'
            (jasminSemTraced.clone_tower cv ct oldDest rs0) h2

/-! ## Promotion: `jasminSem ⟹ ∃ t, jasminSemTraced` -/

/-- Promotion: every `jasminSem` derivation has a corresponding
    `jasminSemTraced` derivation with some trace. The trace is
    determined by the proof structure (concretely: the dynamic
    branch decisions in `if_true`/`if_false`). -/
theorem jasminSem.toTraced (leafSpec : LeafSpec)
    {body : Cmd} {rs rs' : RustState}
    (h : jasminSem leafSpec body rs rs') :
    ∃ t : LeakTrace, jasminSemTraced leafSpec body rs t rs' := by
  induction h with
  | nil rs0 => exact ⟨[], jasminSemTraced.nil rs0⟩
  | cons i is rs0 rs1 rs0' _hi _his ih1 ih2 =>
    obtain ⟨t1, h1'⟩ := ih1
    obtain ⟨t2, h2'⟩ := ih2
    exact ⟨t1 ++ t2, jasminSemTraced.cons i is rs0 t1 rs1 t2 rs0' h1' h2'⟩
  | assgn_parr_init x t' rs0 =>
    exact ⟨_, jasminSemTraced.assgn_parr_init x t' rs0⟩
  | assgn_u64_zero x rs0 =>
    exact ⟨_, jasminSemTraced.assgn_u64_zero x rs0⟩
  | assgn_u64_val x v rs0 =>
    exact ⟨_, jasminSemTraced.assgn_u64_val x v rs0⟩
  | if_true e ct cf rs0 rs0' v hv hne _hct ih =>
    obtain ⟨tInner, h'⟩ := ih
    exact ⟨_, jasminSemTraced.if_true e ct cf rs0 rs0' v tInner hv hne h'⟩
  | if_false e ct cf rs0 rs0' h0 _hcf ih =>
    obtain ⟨tInner, h'⟩ := ih
    exact ⟨_, jasminSemTraced.if_false e ct cf rs0 rs0' tInner h0 h'⟩
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    exact ⟨_, jasminSemTraced.call_oracle f dest args rs0 oldDestV argList hLk hArgs
                                            hArgsTyped⟩
  | limb_store_oracle loc idx v rs0 oldDestV hLk =>
    exact ⟨_, jasminSemTraced.limb_store_oracle loc idx v rs0 oldDestV hLk⟩
  | clone_tower cv ct oldDest rs0 =>
    exact ⟨_, jasminSemTraced.clone_tower cv ct oldDest rs0⟩

/-! ## Unified-trace producer for traced derivations

Given a `jasminSemTraced` execution that ends at state `rs'` with leak
trace `t`, the corresponding `UnifiedTrace` event list is `t` lifted
through `LeakTrace.toUnifiedTrace` plus a terminal `.ret ⟨RustState, rs'⟩`.

This connects the dynamic trace (with branch decisions) to the unified
alphabet from `UnifiedTrace.lean`. -/

open CatCrypt.Crypto.SecureCompilation.UnifiedTrace
open UCMonad.ITreeNUC (emptyEvSig)

/-- Embed a dynamic Jasmin leak trace + final state into the unified
    alphabet. -/
def jasminSemTraced.toUnifiedTrace (t : LeakTrace) (rs' : RustState) :
    UnifiedTrace emptyEvSig LeakEvent Empty :=
  LeakTrace.toUnifiedTrace (E := emptyEvSig) (MemTy := Empty) t
    ++ [Event.ret ⟨RustState, rs'⟩]

/-- Round-trip: projecting the unified trace back to a leak trace
    recovers the original. Same shape as `Cmd.toUnifiedTrace_leak_proj`. -/
theorem jasminSemTraced.toUnifiedTrace_leak_proj
    (t : LeakTrace) (rs' : RustState) :
    UnifiedTrace.toLeakTrace (jasminSemTraced.toUnifiedTrace t rs') = t := by
  unfold jasminSemTraced.toUnifiedTrace
  induction t with
  | nil => rfl
  | cons l t ih =>
    show l :: UnifiedTrace.toLeakTrace
              (LeakTrace.toUnifiedTrace t ++ [Event.ret ⟨RustState, rs'⟩]) = l :: t
    rw [ih]

/-! ## Static-dynamic correspondence on the Cif-free subset (A1.14)

For Jasmin Cmds with no `Cif` (or other branching) at the top level,
the dynamic `jasminSemTraced` trace equals the structural
`JasminSem.Cmd.leakTrace`. This is the Jasmin-side mirror of
`RustExecTraced.straightLine_trace_eq`. -/

/-- Predicate: this `InstrR` introduces no dynamic branching. -/
def instrCifFree : InstrR → Bool
  | .Cif _ _ _      => false
  | .Cwhile _ _ _   => false
  | .Cfor _ _ _     => false
  | .Cassgn _ _ _ _ => true
  | .Copn _ _ _ _   => true
  | .Ccall _ _ _ _  => true

/-- Predicate: this `Cmd` has no dynamic branching at any top-level
    position. (The verified-middle straight-line subset.) -/
def cmdCifFree (body : Cmd) : Bool :=
  body.all instrCifFree

@[simp] theorem cmdCifFree_nil : cmdCifFree [] = true := rfl

@[simp] theorem cmdCifFree_cons (i : InstrR) (is : Cmd) :
    cmdCifFree (i :: is) = (instrCifFree i && cmdCifFree is) := by
  simp [cmdCifFree]

/-- **A1.14**: on the Cif-free subset, the dynamic Jasmin trace
    coincides with the structural Jasmin leak trace. -/
theorem jasminSemTraced.cifFree_trace_eq {leafSpec : LeafSpec}
    {body : Cmd} {rs rs' : RustState} {t : LeakTrace}
    (hCF : cmdCifFree body = true)
    (h : jasminSemTraced leafSpec body rs t rs') :
    t = JasminSem.Cmd.leakTrace body := by
  induction h with
  | nil _ => rfl
  | cons i is _rs0 _t1 _rs1 _t2 _rs0' _hi _his ih1 ih2 =>
    simp only [cmdCifFree_cons, Bool.and_eq_true] at hCF
    show _ ++ _ = JasminSem.Cmd.leakTrace (i :: is)
    simp only [JasminSem.Cmd.leakTrace_cons]
    rw [ih1 (by simp [cmdCifFree, hCF.1]),
        ih2 hCF.2]
    -- Goal now: (per-i trace) ++ (per-is trace) = (per-i tag :: per-is tag-list)
    -- where per-i trace is `[InstrR.leakEvent i]` from the singleton-Cmd
    -- jasminSemTraced rule (assgn_parr_init / call_oracle / etc. all
    -- emit a list with exactly one event matching `InstrR.leakEvent`
    -- on cifFree InstrRs).
    show (JasminSem.Cmd.leakTrace [i]) ++ (JasminSem.Cmd.leakTrace is)
       = JasminSem.InstrR.leakEvent i :: JasminSem.Cmd.leakTrace is
    simp [JasminSem.Cmd.leakTrace]
  | assgn_parr_init x t' rs0 => rfl
  | assgn_u64_zero x rs0 => rfl
  | assgn_u64_val x v rs0 => rfl
  | if_true _ _ _ _ _ _ _ _ _ _ _ =>
    simp [cmdCifFree, instrCifFree] at hCF
  | if_false _ _ _ _ _ _ _ _ _ =>
    simp [cmdCifFree, instrCifFree] at hCF
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs hArgsTyped => rfl
  | limb_store_oracle loc idx v rs0 oldDestV hLk => rfl
  | clone_tower cv ct oldDest rs0 => rfl

/- The cross-stage dynamic correspondence (source-dynamic ↔ target-dynamic
   on the straight-line subset) chains A1.14 (above) with A1.13
   (`RustExecTraced.straightLine_traces_match_jasmin_static` from
   `RustExecTraced.lean`). Stated and proven there since both sides are
   accessible from that file. -/

/-! ## Refactored form: `jasminSemTracedSingle` + `jasminSemTraced'`

Path-1 refactor for A1.18 determinism. The original `jasminSemTraced`
has cons/single-instr overlap (for `body = [i]`, both `cons (i, [])` and
the matching single-instr rule produce a derivation). The refactored
form factors the per-InstrR rules into a separate inductive
`jasminSemTracedSingle` and uses a single `cons` rule that takes
`Single + Cmd` rather than `Cmd + Cmd`. This eliminates the overlap:
every derivation of `i :: is` decomposes uniquely as
"single step on `i`, then cmd-level recursion on `is`".

`jasminSemTraced'` will be proven equivalent to `jasminSemTraced`
(both directions), then determinism is proved on `jasminSemTraced'`
and transferred back via the bridge. -/

mutual

/-- Per-instruction step relation. One constructor per `InstrR` shape
    that the verified-middle subset uses. No cons; no list. -/
inductive jasminSemTracedSingle (leafSpec : LeafSpec) :
    InstrR → RustState → LeakTrace → RustState → Prop where
  | assgn_parr_init : ∀ x t (n tag : Nat) rs,
      n = t.storageBytes → tag = t.byteSize →
      jasminSemTracedSingle leafSpec
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sarr n },
                          info := { towerTag := tag } })
                 .AT_none (.sarr n) (.Parr_init n))
        rs [LeakEvent.pureOp "Cassgn"] (rsSetTower rs x ⟨t, default⟩)
  | assgn_u64_zero : ∀ x rs,
      jasminSemTracedSingle leafSpec
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64) (.Pconst 0))
        rs [LeakEvent.pureOp "Cassgn"] (rsSetScalar rs x 0)
  | assgn_u64_val : ∀ x (v : Nat) rs,
      jasminSemTracedSingle leafSpec
        (.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 }, info := {} })
                 .AT_none (.sword .U64)
                 (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int))))
        rs [LeakEvent.pureOp "Cassgn"] (rsSetScalar rs x v)
  /-- `Cif` true branch — emits the `Cif` tag, then `branch:true`,
      then the inner-branch trace. The inner branch is a `Cmd`-level
      derivation (`jasminSemTraced'`), so this constructor mentions
      that companion type. -/
  | if_true : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState) (v : Nat)
                (tInner : LeakTrace),
      rs.rsScalar e = v → v ≠ 0 →
      jasminSemTraced' leafSpec ct rs tInner rs' →
      jasminSemTracedSingle leafSpec
        (.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf)
        rs (LeakEvent.pureOp "Cif" :: branchTag true :: tInner) rs'
  | if_false : ∀ (e : String) (ct cf : Cmd) (rs rs' : RustState)
                  (tInner : LeakTrace),
      rs.rsScalar e = 0 →
      jasminSemTraced' leafSpec cf rs tInner rs' →
      jasminSemTracedSingle leafSpec
        (.Cif (.Papp2 (.Oneq .U64)
               (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                 info := {} }, gs := false })
               (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf)
        rs (LeakEvent.pureOp "Cif" :: branchTag false :: tInner) rs'
  | call_oracle : ∀ (f : String) (dest : Located)
                    (destVar' : String) (destM destTag : Nat)
                    (args : List Located)
                    (rs : RustState) (oldDestV : RustVal dest.locDst)
                    (argList : List (Σ t, RustVal t)),
      destVar' = dest.locVar →
      destM = dest.locSrc.storageBytes →
      destTag = dest.locSrc.byteSize →
      locatedLookup rs dest = some oldDestV →
      argList = args.filterMap (fun a => rs.rsTower a.locVar) →
      -- Option-A type-recovery: each arg's locDst matches the stored
      -- Sigma type at its locVar. Closes the structural non-determinism
      -- by tying args.map (·.locDst) to rs (which two derivations share).
      (∀ a ∈ args, ∃ v, rs.rsTower a.locVar = some ⟨a.locDst, v⟩) →
      jasminSemTracedSingle leafSpec
        (.Ccall .DoNotInline
                [.Lvar { var := { vname := destVar', vtype := .sarr destM },
                         info := { towerTag := destTag } }]
                { name := f } (args.map locToPExpr))
        rs [LeakEvent.pureOp "Ccall"]
        (locatedUpdate rs dest
              (leafSpec.call f dest.locDst (args.map (·.locDst)) oldDestV argList))
  | limb_store_oracle : ∀ (loc : Located) (locVar' : String) (m mTag : Nat)
                         (idx : Nat) (v : BitVec 64)
                         (rs : RustState) (oldDestV : RustVal loc.locDst),
      locVar' = loc.locVar →
      m = loc.locSrc.storageBytes →
      mTag = loc.locSrc.byteSize →
      locatedLookup rs loc = some oldDestV →
      jasminSemTracedSingle leafSpec
        (.Copn [.Lvar { var := { vname := locVar', vtype := .sarr m },
                        info := { towerTag := mTag } }]
               .AT_none (.Oasm { name := "STORE64" })
               [.Pvar { gv := { var := { vname := locVar', vtype := .sarr m },
                                info := { towerTag := mTag } }, gs := false },
                .Pconst idx, .Pconst v.toNat])
        rs [LeakEvent.pureOp "Copn"]
        (locatedUpdate rs loc (leafSpec.limbStore loc oldDestV idx v))
  | clone_tower : ∀ (cloneVar : String) (cloneTy : TowerType) (oldDest : Located)
                    (oldVar' : String) (oldM oldTag : Nat) (n cloneTag : Nat)
                    (rs : RustState),
      oldVar' = oldDest.locVar →
      oldM = oldDest.locSrc.storageBytes →
      oldTag = oldDest.locSrc.byteSize →
      n = cloneTy.storageBytes →
      cloneTag = cloneTy.byteSize →
      jasminSemTracedSingle leafSpec
        (.Copn [.Lvar { var := { vname := cloneVar, vtype := .sarr n },
                         info := { towerTag := cloneTag } }] .AT_none
              (.Oasm { name := "CLONE_TOWER" })
              [.Pvar { gv := { var := { vname := oldVar', vtype := .sarr oldM },
                               info := { towerTag := oldTag } }, gs := false }])
        rs [LeakEvent.pureOp "Copn"]
        (rsSetTower rs cloneVar
             ((rs.rsTower oldDest.locVar).getD ⟨cloneTy, default⟩))

/-- Refactored Cmd-level trace-emitting semantics: `cons` takes a
    single-step plus a Cmd-level recursion. No overlap with
    single-instruction rules — each `Cmd` has at most one canonical
    derivation shape. -/
inductive jasminSemTraced' (leafSpec : LeafSpec) :
    Cmd → RustState → LeakTrace → RustState → Prop where
  | nil : ∀ rs, jasminSemTraced' leafSpec [] rs [] rs
  | cons : ∀ i is rs t1 rs1 t2 rs',
      jasminSemTracedSingle leafSpec i rs t1 rs1 →
      jasminSemTraced' leafSpec is rs1 t2 rs' →
      jasminSemTraced' leafSpec (i :: is) rs (t1 ++ t2) rs'

end

/-- Inversion: a refactored derivation on `[i]` decomposes uniquely into
    a single-step. -/
theorem jasminSemTraced'.singleton_inv {leafSpec : LeafSpec}
    {i : InstrR} {rs rs' : RustState} {t : LeakTrace}
    (h : jasminSemTraced' leafSpec [i] rs t rs') :
    jasminSemTracedSingle leafSpec i rs t rs' := by
  cases h with
  | cons _i _is _rs t1 rs1 t2 _rs' h_single h_rest =>
    -- _is = [] from unification; h_rest : jasminSemTraced' [] rs1 t2 rs'
    cases h_rest
    -- t2 = [], rs' = rs1; trace = t1 ++ [] = t1
    simpa using h_single

/-- Sequential composition: `jasminSemTraced'` concatenates over list
    append. Mirror of `jasminSemTraced_seq_compose`. Proved by induction
    on the list `l1` (cases on the derivation per element), since
    Lean's `induction` tactic doesn't support mutual inductives directly. -/
theorem jasminSemTraced'_seq_compose
    (leafSpec : LeafSpec) (l1 l2 : Cmd) :
    ∀ (rs r1 rs' : RustState) (t1 t2 : LeakTrace),
      jasminSemTraced' leafSpec l1 rs t1 r1 →
      jasminSemTraced' leafSpec l2 r1 t2 rs' →
      jasminSemTraced' leafSpec (l1 ++ l2) rs (t1 ++ t2) rs' := by
  induction l1 with
  | nil =>
    intro rs r1 rs' t1 t2 h1 h2
    cases h1
    simpa using h2
  | cons i is ih =>
    intro rs r1 rs' t1 t2 h1 h2
    cases h1 with
    | cons _i _is _rs t1' rs1 t2' _r1 h_single h_rest =>
      rw [List.cons_append, List.append_assoc]
      exact jasminSemTraced'.cons i (is ++ l2) rs t1' rs1 (t2' ++ t2) rs'
              h_single (ih rs1 r1 rs' t2' t2 h_rest h2)

/-- **Trace-splitting** (inverse of `jasminSemTraced'_seq_compose`):
    a derivation on `l1 ++ l2` decomposes into a derivation on `l1`
    followed by one on `l2`, with concatenated traces. Foundation for
    the reverse compiler-correctness theorem (A1.16'). -/
theorem jasminSemTraced'_split
    (leafSpec : LeafSpec) :
    ∀ (l1 l2 : Cmd) (rs rs' : RustState) (t : LeakTrace),
      jasminSemTraced' leafSpec (l1 ++ l2) rs t rs' →
      ∃ (r1 : RustState) (t1 t2 : LeakTrace),
        t = t1 ++ t2 ∧
        jasminSemTraced' leafSpec l1 rs t1 r1 ∧
        jasminSemTraced' leafSpec l2 r1 t2 rs'
  | [], l2, rs, rs', t, h => by
    refine ⟨rs, [], t, by simp, jasminSemTraced'.nil rs, ?_⟩
    simpa using h
  | i :: is, l2, rs, rs', t, h => by
    rw [List.cons_append] at h
    cases h with
    | cons _i _is _rs t1' rs1 t2' _rs' h_single h_rest =>
      obtain ⟨r1, t2, t3, ht, hL1tail, hL2⟩ :=
        jasminSemTraced'_split leafSpec is l2 rs1 rs' t2' h_rest
      refine ⟨r1, t1' ++ t2, t3, ?_, ?_, hL2⟩
      · simp [ht, List.append_assoc]
      · exact jasminSemTraced'.cons i is rs t1' rs1 t2 r1 h_single hL1tail

/-! ### Bridge: `jasminSemTraced ↔ jasminSemTraced'`

Both directions of equivalence. The forward direction (original →
refactored) folds each single-instr rule into a cons + Single + nil
pattern; the backward direction (refactored → original) reverses it. -/

/-- Forward direction: original `jasminSemTraced` derivations lift to
    `jasminSemTraced'`. Each single-instr rule maps via cons. -/
theorem jasminSemTraced.toPrime
    {leafSpec : LeafSpec} {body : Cmd} {rs rs' : RustState} {t : LeakTrace}
    (h : jasminSemTraced leafSpec body rs t rs') :
    jasminSemTraced' leafSpec body rs t rs' := by
  induction h with
  | nil rs0 => exact jasminSemTraced'.nil rs0
  | cons _i _is _rs _t1 _rs1 _t2 _rs' _h1 _h2 ih1 ih2 =>
    -- ih1 : jasminSemTraced' [i] rs t1 rs1
    -- ih2 : jasminSemTraced' is rs1 t2 rs'
    -- Need: jasminSemTraced' (i :: is) rs (t1 ++ t2) rs'
    -- Use jasminSemTraced'.singleton_inv to extract the Single, then cons.
    have h_single := jasminSemTraced'.singleton_inv ih1
    exact jasminSemTraced'.cons _ _ _ _ _ _ _ h_single ih2
  | assgn_parr_init x t' rs0 =>
    -- Body = [Cassgn-Parr_init]; build cons(Single, nil).
    have h_single := @jasminSemTracedSingle.assgn_parr_init leafSpec x t'
                       t'.storageBytes t'.byteSize rs0 rfl rfl
    have : jasminSemTraced' leafSpec
              [.Cassgn (.Lvar { var := { vname := x, vtype := .sarr t'.storageBytes },
                                info := { towerTag := t'.byteSize } })
                       .AT_none (.sarr t'.storageBytes) (.Parr_init t'.storageBytes)]
              rs0
              ([LeakEvent.pureOp "Cassgn"] ++ [])
              (rsSetTower rs0 x ⟨t', default⟩) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single
        (jasminSemTraced'.nil _)
    simpa using this
  | assgn_u64_zero x rs0 =>
    have h_single := @jasminSemTracedSingle.assgn_u64_zero leafSpec x rs0
    have : jasminSemTraced' leafSpec
              [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                                info := {} }) .AT_none (.sword .U64) (.Pconst 0)]
              rs0
              ([LeakEvent.pureOp "Cassgn"] ++ [])
              (rsSetScalar rs0 x 0) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single
        (jasminSemTraced'.nil _)
    simpa using this
  | assgn_u64_val x v rs0 =>
    have h_single := @jasminSemTracedSingle.assgn_u64_val leafSpec x v rs0
    have : jasminSemTraced' leafSpec
              [.Cassgn (.Lvar { var := { vname := x, vtype := .sword .U64 },
                                info := {} }) .AT_none (.sword .U64)
                       (.Papp1 (.Oword_of_int .U64) (.Pconst (v : Int)))]
              rs0
              ([LeakEvent.pureOp "Cassgn"] ++ [])
              (rsSetScalar rs0 x v) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single
        (jasminSemTraced'.nil _)
    simpa using this
  | if_true e ct cf rs0 rs0' v tInner hv hne _hct ih_ct =>
    have h_single := @jasminSemTracedSingle.if_true leafSpec e ct cf rs0 rs0' v tInner hv hne ih_ct
    have : jasminSemTraced' leafSpec
              [.Cif (.Papp2 (.Oneq .U64)
                     (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                       info := {} }, gs := false })
                     (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
              rs0
              ((LeakEvent.pureOp "Cif" :: branchTag true :: tInner) ++ [])
              rs0' :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single (jasminSemTraced'.nil _)
    simpa using this
  | if_false e ct cf rs0 rs0' tInner h0 _hcf ih_cf =>
    have h_single := @jasminSemTracedSingle.if_false leafSpec e ct cf rs0 rs0' tInner h0 ih_cf
    have : jasminSemTraced' leafSpec
              [.Cif (.Papp2 (.Oneq .U64)
                     (.Pvar { gv := { var := { vname := e, vtype := .sword .U64 },
                                       info := {} }, gs := false })
                     (.Papp1 (.Oword_of_int .U64) (.Pconst 0))) ct cf]
              rs0
              ((LeakEvent.pureOp "Cif" :: branchTag false :: tInner) ++ [])
              rs0' :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single (jasminSemTraced'.nil _)
    simpa using this
  | call_oracle f dest args rs0 oldDestV argList hLk hArgs hArgsTyped =>
    have h_single := @jasminSemTracedSingle.call_oracle leafSpec f dest
                       dest.locVar dest.locSrc.storageBytes dest.locSrc.byteSize
                       args rs0 oldDestV argList
                       rfl rfl rfl hLk hArgs hArgsTyped
    have : jasminSemTraced' leafSpec
              [.Ccall .DoNotInline
                      [.Lvar { var := { vname := dest.locVar,
                                         vtype := .sarr dest.locSrc.storageBytes },
                               info := { towerTag := dest.locSrc.byteSize } }]
                      { name := f } (args.map locToPExpr)]
              rs0
              ([LeakEvent.pureOp "Ccall"] ++ [])
              (locatedUpdate rs0 dest
                  (leafSpec.call f dest.locDst (args.map (·.locDst))
                                  oldDestV argList)) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single (jasminSemTraced'.nil _)
    simpa [locToLVal, locToVar, towerToSType] using this
  | limb_store_oracle loc idx v rs0 oldDestV hLk =>
    have h_single := @jasminSemTracedSingle.limb_store_oracle leafSpec
                       loc loc.locVar loc.locSrc.storageBytes loc.locSrc.byteSize
                       idx v rs0 oldDestV
                       rfl rfl rfl hLk
    have : jasminSemTraced' leafSpec
              [.Copn [.Lvar { var := { vname := loc.locVar,
                                        vtype := .sarr loc.locSrc.storageBytes },
                              info := { towerTag := loc.locSrc.byteSize } }]
                     .AT_none (.Oasm { name := "STORE64" })
                     [.Pvar { gv := { var := { vname := loc.locVar,
                                                vtype := .sarr loc.locSrc.storageBytes },
                                       info := { towerTag := loc.locSrc.byteSize } },
                              gs := false },
                      .Pconst idx, .Pconst v.toNat]]
              rs0
              ([LeakEvent.pureOp "Copn"] ++ [])
              (locatedUpdate rs0 loc (leafSpec.limbStore loc oldDestV idx v)) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single (jasminSemTraced'.nil _)
    simpa [locToLVal, locToPExpr, locToVar, locToGVar, towerToSType] using this
  | clone_tower cv ct oldDest rs0 =>
    have h_single := @jasminSemTracedSingle.clone_tower leafSpec cv ct oldDest
                       oldDest.locVar oldDest.locSrc.storageBytes
                       oldDest.locSrc.byteSize ct.storageBytes ct.byteSize rs0
                       rfl rfl rfl rfl rfl
    have : jasminSemTraced' leafSpec
              [.Copn [.Lvar { var := { vname := cv, vtype := .sarr ct.storageBytes },
                              info := { towerTag := ct.byteSize } }] .AT_none
                    (.Oasm { name := "CLONE_TOWER" })
                    [.Pvar { gv := { var := { vname := oldDest.locVar,
                                               vtype := .sarr oldDest.locSrc.storageBytes },
                                      info := { towerTag := oldDest.locSrc.byteSize } },
                             gs := false }]]
              rs0
              ([LeakEvent.pureOp "Copn"] ++ [])
              (rsSetTower rs0 cv
                ((rs0.rsTower oldDest.locVar).getD ⟨ct, default⟩)) :=
      jasminSemTraced'.cons _ _ _ _ _ _ _ h_single (jasminSemTraced'.nil _)
    simpa [locToPExpr, locToGVar, locToVar, towerToSType] using this

/-! ### Backward bridge: refactored → original (term-mode match)

Mutual recursion via term-mode `match`. Each `Single`/`Prime`
constructor maps to the matching `jasminSemTraced` rule;
`Single.if_true`/`if_false` cases recurse mutually through the
`jasminSemTraced'` inner branch. -/

mutual

theorem jasminSemTracedSingle.toOriginal {leafSpec : LeafSpec}
    {i : InstrR} {rs rs' : RustState} {t : LeakTrace}
    (h : jasminSemTracedSingle leafSpec i rs t rs') :
    jasminSemTraced leafSpec [i] rs t rs' :=
  match h with
  | .assgn_parr_init x t' n tag rs0 hn htag =>
    -- Goal: jasminSemTraced [Cassgn (Lvar sarr n, tag) ... (Parr_init n)] rs0 ... rs1
    -- The original rule states the instruction over `t'.storageBytes` /
    -- `t'.byteSize`; the side hypotheses rewrite it to the goal shape.
    hn.symm ▸ htag.symm ▸ jasminSemTraced.assgn_parr_init x t' rs0
  | .assgn_u64_zero x rs0 => jasminSemTraced.assgn_u64_zero x rs0
  | .assgn_u64_val x v rs0 => jasminSemTraced.assgn_u64_val x v rs0
  | .if_true e ct cf rs0 rs0' v tInner hv hne hct =>
    jasminSemTraced.if_true e ct cf rs0 rs0' v tInner hv hne
      (jasminSemTraced'.toOriginal hct)
  | .if_false e ct cf rs0 rs0' tInner h0 hcf =>
    jasminSemTraced.if_false e ct cf rs0 rs0' tInner h0
      (jasminSemTraced'.toOriginal hcf)
  | .call_oracle f dest destVar' destM destTag args rs0 oldDestV argList
                  hVar hM hTag hLk hArgs hArgsTyped =>
    hVar.symm ▸ hM.symm ▸ hTag.symm ▸
      jasminSemTraced.call_oracle f dest args rs0 oldDestV
                            argList hLk hArgs hArgsTyped
  | .limb_store_oracle loc locVar' m mTag idx v rs0 oldDestV hVar hM hTag hLk =>
    hVar.symm ▸ hM.symm ▸ hTag.symm ▸
      jasminSemTraced.limb_store_oracle loc idx v rs0 oldDestV hLk
  | .clone_tower cv ct oldDest oldVar' oldM oldTag n cloneTag rs0
                  hVar hM hOldTag hn hCloneTag =>
    hVar.symm ▸ hM.symm ▸ hOldTag.symm ▸ hn.symm ▸ hCloneTag.symm ▸
      jasminSemTraced.clone_tower cv ct oldDest rs0

theorem jasminSemTraced'.toOriginal {leafSpec : LeafSpec}
    {body : Cmd} {rs rs' : RustState} {t : LeakTrace}
    (h : jasminSemTraced' leafSpec body rs t rs') :
    jasminSemTraced leafSpec body rs t rs' :=
  match h with
  | .nil rs0 => jasminSemTraced.nil rs0
  | .cons i is rs0 t1 rs1 t2 rs0' h_single h_rest =>
    jasminSemTraced.cons i is rs0 t1 rs1 t2 rs0'
      (jasminSemTracedSingle.toOriginal h_single)
      (jasminSemTraced'.toOriginal h_rest)

end

end CatCrypt.Crypto.SecureCompilation.JasminSemTraced
