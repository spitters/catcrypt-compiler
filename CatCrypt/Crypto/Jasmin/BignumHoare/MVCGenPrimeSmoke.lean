/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Tactic.Do
public import CatCrypt.Crypto.Jasmin.BignumHoare
public import CatCrypt.Crypto.Jasmin.BignumHoare.ModP25519Final

/-!
# `mvcgen'` over the bignum interpreter

`mvcgen'` is the Sym-based verification-condition generator that
`Std.Tactic.Do` exposes alongside `mvcgen`. This module connects it to
`bignumExecM`, the `StateT BignumState Option` form of the bignum SSA
interpreter.

## What this module ships

* `BignumTripleM P body Q` — Triple-form alias of `BignumTriple`, in
  `⦃P⦄ body ⦃Q⦄` notation. The bridge uses the partial-correctness form
  `⇓?` (`PostCond.mayThrow`) because `BignumTriple` does not require
  successful termination.
* `bignumTripleM_iff_bignumTriple` — the both-directions bridge, derived
  from `bignumExecM_iff_bignumExec` in `BignumExec.lean`.
* `bignum_mod_p25519_4_correct_triple` — `bignum_mod_p25519_4_correct_universal`
  re-stated in Triple notation through that bridge.
* Nine `@[spec]` step lemmas, one per SSA builder shape of
  `BignumModP25519_4`, and the state transformers they are phrased over.
* `modP25519_register_kernel_triple` — the 26 register instructions of
  `bignum_mod_p25519_4` walked by a single `mvcgen'` call.
* `modP25519_load_prefix_triple` — the five-instruction prefix (zero
  register plus the four input loads) walked by `mvcgen'` and `mspec`.

## Coverage

The step lemmas cover every builder shape of the body. `store64` is a
total state transformer. `load64` is partial: its weakest precondition
is a case split on the 8-byte read, so `mvcgen'` emits a verification
condition at the split and stops. The walk continues by resolving the
split with the caller's load hypothesis and then applying
`stepInstrM_load64_spec` through `mspec`, which steps a `wp`-headed goal
that a second `mvcgen'` call leaves unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.BignumHoare.MVCGenPrimeSmoke

open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.Jasmin.BignumExec
open CatCrypt.Crypto.Jasmin.MemoryModel
open Std.Do

/-! ## §1  Notation bridge

Bridges `BignumTriple` (the partial-correctness state-relation form
used across the bignum tree) with `Std.Do.Triple` / `⦃P⦄ body ⦃Q⦄`
notation. The bridge uses `⇓?` (`PostCond.mayThrow`) because
`BignumTriple` is partial-correctness: it does not require successful
termination.

```
BignumTriple P body Q  :=  ∀ s s', P s → bignumExec body s = some s' → Q s'

BignumTripleM P body Q :=  ⦃fun s => ⌜P s⌝⦄
                             bignumExecM emptyRegistry body
                           ⦃⇓? _ => fun s => ⌜Q s⌝⦄
```

The two are equivalent via the `bignumExecM_iff_bignumExec`
bridge in `BignumExec.lean`. -/

/-- Triple-form alias of `BignumTriple`, in
    `⦃P⦄ body ⦃Q⦄` notation. Partial-correctness form via
    `⇓?` (`PostCond.mayThrow`). -/
def BignumTripleM (P : BignumState → Prop) (body : List InstrR)
    (Q : BignumState → Prop) : Prop :=
  Triple (bignumExecM emptyRegistry body)
         (fun s => ⌜P s⌝)
         (⇓? _ => fun s => ⌜Q s⌝)

/-- Forward bridge: a `BignumTripleM` lifts back to the
    state-relation form. Successful runs of `bignumExec` satisfy
    the postcondition. -/
theorem bignumTripleM_to_relation
    {P Q : BignumState → Prop} {body : List InstrR}
    (h : BignumTripleM P body Q) :
    ∀ s s', P s → bignumExec body s = some s' → Q s' := by
  intro s s' hP hExec
  simp only [BignumTripleM, Triple, Std.Do.WP.wp,
             Std.Do.PredTrans.apply_pushArg, Std.Do.PredTrans.apply_pushOption,
             Std.Do.PredTrans.apply_Pure_pure, PostCond.mayThrow,
             Id.run, OptionT.run, Option.instWP._aux_1, StateT.run] at h
  have hRun : bignumExecM emptyRegistry body s = some ((), s') :=
    (bignumExecM_iff_bignumExec body s s').mpr hExec
  have h' := h s hP
  dsimp only at h'
  rw [hRun] at h'
  exact h'

/-- Reverse bridge: a `BignumTriple` lifts to a `BignumTripleM`. -/
theorem bignumTripleM_of_relation
    {P Q : BignumState → Prop} {body : List InstrR}
    (h : ∀ s s', P s → bignumExec body s = some s' → Q s') :
    BignumTripleM P body Q := by
  simp only [BignumTripleM, Triple, Std.Do.WP.wp,
             Std.Do.PredTrans.apply_pushArg, Std.Do.PredTrans.apply_pushOption,
             Std.Do.PredTrans.apply_Pure_pure, PostCond.mayThrow,
             Id.run, OptionT.run, Option.instWP._aux_1, StateT.run]
  intro s hP
  dsimp only
  split
  · rename_i a hRun
    obtain ⟨_, s'⟩ := a
    have hExec := (bignumExecM_iff_bignumExec body s s').mp hRun
    exact h s s' hP hExec
  · simp [ExceptConds.true, ExceptConds.const]

/-- `BignumTriple` ↔ `BignumTripleM`. The two
    shapes are interconvertible. -/
theorem bignumTripleM_iff_bignumTriple
    (P : BignumState → Prop) (body : List InstrR) (Q : BignumState → Prop) :
    BignumTripleM P body Q ↔ BignumTriple P body Q := by
  constructor
  · intro h
    intro s s' hP hStep
    exact bignumTripleM_to_relation h s s' hP hStep
  · intro h
    exact bignumTripleM_of_relation h

/-! ## §2  Smoke test on `bignum_mod_p25519_4`

Re-states the existing universal correctness theorem
`CatCrypt.Crypto.Jasmin.BignumHoare.bignum_mod_p25519_4_correct_universal`
(in `BignumHoare.lean`) using the `⦃P⦄ body ⦃Q⦄`
notation, by transporting through `bignumTripleM_iff_bignumTriple`.

The existing proof's content is preserved; only the surface syntax
changes. §3 below reaches the same statement's register-only kernel
directly through `mvcgen'`. -/

/-- `bignum_mod_p25519_4_correct_universal` re-stated in Triple
notation via the partial-correctness bridge.

Proved by `bignumTripleM_of_relation` applied to the existing
state-relation universal. -/
theorem bignum_mod_p25519_4_correct_triple
    (base_a base_op : UInt64)
    (h_disj : MemoryModel.Disjoint
                (MemoryModel.range base_a 32)
                (MemoryModel.range base_op 32)) :
    BignumTripleM
      (CatCrypt.Crypto.Jasmin.BignumHoare.bignumModPre base_a base_op)
      S2NBignumSSA.BignumModP25519_4.body
      (CatCrypt.Crypto.Jasmin.BignumHoare.bignumModPost base_a base_op) := by
  apply bignumTripleM_of_relation
  exact CatCrypt.Crypto.Jasmin.BignumHoare.bignum_mod_p25519_4_correct_universal
          base_a base_op h_disj

/-! ## §3  `mvcgen'` over the SSA instruction set

The `@[spec]` step lemmas below let `mvcgen'` symbolically execute a
straight-line block of `bignumExecM` and emit a single verification
condition carrying the block's algebraic content.

The lemmas cover the nine SSA builder shapes of `BignumModP25519_4`:
`assignConst`, `copy64`, `assignBin` at `Oland` / `Olor` / `Olxor`,
`subCopn`, `sbbCopn`, `store64`, and `load64`. The first eight are
total state transformers. `load64` is partial: its weakest precondition
is a case split on the 8-byte read, and `mvcgen'` emits a verification
condition at that split instead of continuing the walk. -/

/-! ### Per-shape state transformers

Each SSA builder shape gets a named state transformer
in which the pre-state occurs exactly once. The `@[spec]` lemmas below
phrase the post-state through these names, so the symbolic state
`mvcgen'` carries across a straight-line block is a chain whose size is
linear in the block length. Phrasing a step inline (`setReg s x
(s.regs a &&& s.regs b)`) duplicates the pre-state per operand and makes
that chain grow exponentially. -/

/-- The state transformer of `S2NBignumSSA.assignConst x k`. -/
def stepConst (s : BignumState) (x : String) (k : Int) : BignumState :=
  setReg s x (BitVec.ofInt 64 k)

/-- The state transformer of `BignumModP25519_4.copy64 dst src`. -/
def stepCopy (s : BignumState) (dst src : String) : BignumState :=
  setReg s dst (s.regs src)

/-- The state transformer of `S2NBignumSSA.assignBin x op a b`, with `f`
    the semantics of `op` on the two register operands. -/
def stepBin (s : BignumState) (x : String)
    (f : BitVec 64 → BitVec 64 → BitVec 64) (a b : String) : BignumState :=
  setReg s x (f (s.regs a) (s.regs b))

/-- The state transformer of `BignumModP25519_4.subCopn cfOut rOut a b`:
    the borrow lands in `cfOut`, the difference in `rOut`. -/
def stepSub (s : BignumState) (cfOut rOut a b : String) : BignumState :=
  let p := subBorrow (s.regs a) (s.regs b)
  setReg (setReg s cfOut p.1) rOut p.2

/-- The state transformer of `BignumModP25519_4.sbbCopn cfOut rOut a b cin`:
    the borrow lands in `cfOut`, the difference in `rOut`. -/
def stepSbb (s : BignumState) (cfOut rOut a b cin : String) : BignumState :=
  let p := subBorrowIn (s.regs a) (s.regs b) (s.regs cin)
  setReg (setReg s cfOut p.1) rOut p.2

/-- The address a `BignumModP25519_4.load64` / `store64` at base register
    `base` and constant offset `k` resolves to. -/
def stepAddr (s : BignumState) (base : String) (k : Int) : UInt64 :=
  UInt64.ofNat ((s.regs base + BitVec.ofInt 64 k).toNat)

/-- The state transformer of `BignumModP25519_4.load64 x base k` on the
    branch where the 8-byte read at the resolved address returns `w`. -/
def stepLoad (s : BignumState) (x : String) (w : UInt64) : BignumState :=
  setReg s x (BitVec.ofNat 64 w.toNat)

/-- The state transformer of `BignumModP25519_4.store64 base k src`. -/
def stepStore (s : BignumState) (base : String) (k : Int) (src : String) :
    BignumState :=
  storeMem s (stepAddr s base k) (UInt64.ofNat (s.regs src).toNat)

theorem assignConst_eq (x : String) (k : Int) :
    S2NBignumSSA.assignConst x k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64) (.Pconst k) := rfl

theorem copy64_eq (dst src : String) :
    S2NBignumSSA.BignumModP25519_4.copy64 dst src =
      .Cassgn (.Lvar { var := S2NBignumSSA.v dst }) .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

theorem assignBin_eq (x : String) (op : SOp2) (a b : String) :
    S2NBignumSSA.assignBin x op a b =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Papp2 op (.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false })
                   (.Pvar { gv := { var := S2NBignumSSA.v b }, gs := false })) := rfl

theorem load64_eq (x base : String) (k : Int) :
    S2NBignumSSA.BignumModP25519_4.load64 x base k =
      .Cassgn (.Lvar { var := S2NBignumSSA.v x }) .AT_none (.sword .U64)
        (.Pload .U64 { var := S2NBignumSSA.v base } (.Pconst k)) := rfl

theorem store64_eq (base : String) (k : Int) (src : String) :
    S2NBignumSSA.BignumModP25519_4.store64 base k src =
      .Cassgn (.Lmem .U64 { var := S2NBignumSSA.v base } (.Pconst k))
        .AT_none (.sword .U64)
        (.Pvar { gv := { var := S2NBignumSSA.v src }, gs := false }) := rfl

theorem subCopn_eq (cfOut rOut a b : String) :
    S2NBignumSSA.BignumModP25519_4.subCopn cfOut rOut a b =
      .Copn [.Lnone {} (.sword .U64), .Lvar { var := S2NBignumSSA.v cfOut },
             .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
             .Lvar { var := S2NBignumSSA.v rOut }] .AT_none (.Oasm ⟨"SUB_64"⟩)
        [.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false },
         .Pvar { gv := { var := S2NBignumSSA.v b }, gs := false }] := rfl

theorem sbbCopn_eq (cfOut rOut a b cin : String) :
    S2NBignumSSA.BignumModP25519_4.sbbCopn cfOut rOut a b cin =
      .Copn [.Lnone {} (.sword .U64), .Lvar { var := S2NBignumSSA.v cfOut },
             .Lnone {} (.sword .U64), .Lnone {} (.sword .U64), .Lnone {} (.sword .U64),
             .Lvar { var := S2NBignumSSA.v rOut }] .AT_none (.Oasm ⟨"SBB_64"⟩)
        [.Pvar { gv := { var := S2NBignumSSA.v a }, gs := false },
         .Pvar { gv := { var := S2NBignumSSA.v b }, gs := false },
         .Pvar { gv := { var := S2NBignumSSA.v cin }, gs := false }] := rfl

/-! ### `@[spec]` step lemmas

One lemma per register-writing SSA builder shape. Each states the
weakest precondition of the corresponding `stepInstrM` as the
postcondition at the successor state, which is the form `mvcgen'`
chains: after applying the lemma the goal is again `wp⟦·⟧`-headed, so
the walk continues into the rest of the block instead of stopping at a
verification condition. -/

@[spec]
theorem stepInstrM_assignConst_spec (r : BignumRegistry) (x : String) (k : Int)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.assignConst x k))
      spred(fun s => Q.1 () (stepConst s x k))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             assignConst_eq, S2NBignumSSA.v, execInstr, evalPExpr]
  exact h

@[spec]
theorem stepInstrM_copy64_spec (r : BignumRegistry) (dst src : String)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.BignumModP25519_4.copy64 dst src))
      spred(fun s => Q.1 () (stepCopy s dst src))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             copy64_eq, S2NBignumSSA.v, execInstr, evalPExpr]
  exact h

@[spec]
theorem stepInstrM_assignBinLand_spec (r : BignumRegistry) (x a b : String) (w : WSize)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.assignBin x (.Oland w) a b))
      spred(fun s => Q.1 () (stepBin s x (· &&& ·) a b))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             assignBin_eq, S2NBignumSSA.v, execInstr, evalPExpr]
  exact h

@[spec]
theorem stepInstrM_assignBinLor_spec (r : BignumRegistry) (x a b : String) (w : WSize)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.assignBin x (.Olor w) a b))
      spred(fun s => Q.1 () (stepBin s x (· ||| ·) a b))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             assignBin_eq, S2NBignumSSA.v, execInstr, evalPExpr]
  exact h

@[spec]
theorem stepInstrM_assignBinLxor_spec (r : BignumRegistry) (x a b : String) (w : WSize)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.assignBin x (.Olxor w) a b))
      spred(fun s => Q.1 () (stepBin s x (· ^^^ ·) a b))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             assignBin_eq, S2NBignumSSA.v, execInstr, evalPExpr]
  exact h

@[spec]
theorem stepInstrM_subCopn_spec (r : BignumRegistry) (cfOut rOut a b : String)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.BignumModP25519_4.subCopn cfOut rOut a b))
      spred(fun s => Q.1 () (stepSub s cfOut rOut a b))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             subCopn_eq, S2NBignumSSA.v, execInstr, evalPExpr, writeSubBundle]
  exact h

@[spec]
theorem stepInstrM_sbbCopn_spec (r : BignumRegistry) (cfOut rOut a b cin : String)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.BignumModP25519_4.sbbCopn cfOut rOut a b cin))
      spred(fun s => Q.1 () (stepSbb s cfOut rOut a b cin))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             sbbCopn_eq, S2NBignumSSA.v, execInstr, evalPExpr, writeSubBundle]
  exact h

@[spec]
theorem stepInstrM_store64_spec (r : BignumRegistry) (base : String) (k : Int)
    (src : String)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.BignumModP25519_4.store64 base k src))
      spred(fun s => Q.1 () (stepStore s base k src))
      Q := by
  intro s h
  simp only [BignumExec.wp_apply_stateT_option, StateT.run, stepInstrM,
             store64_eq, S2NBignumSSA.v, execInstr, evalPExpr, resolveAddr]
  exact h

@[spec]
theorem stepInstrM_load64_spec (r : BignumRegistry) (x base : String) (k : Int)
    {Q : PostCond Unit (.arg BignumState (.except PUnit .pure))} :
    Triple (stepInstrM r (S2NBignumSSA.BignumModP25519_4.load64 x base k))
      (fun s =>
        match load64Mem s.mem (stepAddr s base k) with
        | some w => Q.1 () (stepLoad s x w)
        | none => Q.2.1 PUnit.unit)
      Q := by
  have key : ∀ s : BignumState,
      (match load64Mem s.mem (stepAddr s base k) with
        | some w => Q.1 () (stepLoad s x w)
        | none => Q.2.1 PUnit.unit)
        = (wp (m := StateT BignumState Option)
             (stepInstrM r (S2NBignumSSA.BignumModP25519_4.load64 x base k))).apply Q s := by
    intro s
    rw [BignumExec.wp_apply_stateT_option]
    simp only [StateT.run, stepInstrM, load64_eq, S2NBignumSSA.v, execInstr,
               evalPExpr, resolveAddr, stepAddr, stepLoad,
               Option.bind_eq_bind, Option.bind_some]
    cases load64Mem s.mem (UInt64.ofNat ((s.regs base + BitVec.ofInt 64 k).toNat)) <;> rfl
  rw [Triple, funext key]

/-! ### The kernel walk

`WPMonad BignumM` is derived by instance search from
`StateT.instWPMonad` and `Option.instWPMonad`. -/

example : WPMonad BignumM (.arg BignumState (.except PUnit .pure)) :=
  inferInstance

/-- `mvcgen'` applies to `BignumM` triples in partial-correctness
    (`⇓?`) form. -/
example : ⦃fun (_ : BignumState) => ⌜True⌝⦄
    (pure () : BignumM Unit)
    ⦃⇓? _ => fun (_ : BignumState) => ⌜True⌝⦄ := by
  mvcgen'

open CatCrypt.Crypto.Jasmin.BignumHoare in
/-- The register-only kernel of `bignum_mod_p25519_4`: instructions 5
    through 30 of the body, from the four input limbs already in
    `a0`-`a3` and a zeroed `zero`, leave the canonical reduction's limbs
    in `o0`-`o3`.

    `mvcgen'` dispatches the seven `@[spec]` step lemmas above across
    all 26 instructions and emits one verification condition, whose
    algebraic content is `sbb_chain_algoNat`. -/
theorem modP25519_register_kernel_triple (a0 a1 a2 a3 : UInt64) :
    Triple (bignumExecM emptyRegistry
              ((S2NBignumSSA.BignumModP25519_4.body.drop 5).take 26))
      (fun s => ⌜s.regs "zero" = 0 ∧ s.regs "a0" = a0.toBitVec ∧
                 s.regs "a1" = a1.toBitVec ∧ s.regs "a2" = a2.toBitVec ∧
                 s.regs "a3" = a3.toBitVec⌝)
      (⇓? _ => fun s => ⌜(s.regs "o0").toNat + (s.regs "o1").toNat * 2 ^ 64
                          + (s.regs "o2").toNat * 2 ^ 128 + (s.regs "o3").toNat * 2 ^ 192
                        = S2NBignumSSA.BignumModP25519_4.algoNat
                            (a0.toNat + a1.toNat * 2 ^ 64
                              + a2.toNat * 2 ^ 128 + a3.toNat * 2 ^ 192)⌝) := by
  show Triple (bignumExecM emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumModP25519_4.body, List.take, List.drop]
  mvcgen' [bignumExecM_cons, bignumExecM_nil]
  rename_i hs
  obtain ⟨hz, h0, h1, h2, h3⟩ := hs
  simp only [stepConst, stepCopy, stepBin, stepSub, stepSbb, setReg,
             String.reduceEq, ↓reduceIte, hz, h0, h1, h2, h3]
  exact sbb_chain_algoNat a0.toBitVec a1.toBitVec a2.toBitVec a3.toBitVec

/-- The address a `load64`/`store64` off a base register holding a
    `UInt64` pointer resolves to. -/
theorem stepAddr_of_regs (s : BignumState) (base : String) (b : UInt64)
    (k : Int) (h : s.regs base = BitVec.ofNat 64 b.toNat) :
    stepAddr s base k = b + UInt64.ofNat (BitVec.ofInt 64 k).toNat := by
  simp only [stepAddr, h]
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, BitVec.toNat_add, Nat.add_mod]

/-- The load prefix of `bignum_mod_p25519_4`: instructions 0 through 4
    of the body zero the `zero` register and read the four input limbs
    at `base_a` into `a0`-`a3`.

    `mvcgen'` walks the constant step and stops at the first load; each
    remaining load is stepped by `mspec stepInstrM_load64_spec` after
    the caller's load hypothesis resolves the previous split. This is
    the precondition side of `modP25519_register_kernel_triple`. -/
theorem modP25519_load_prefix_triple
    (base_a : UInt64) (a0 a1 a2 a3 : UInt64) :
    Triple (bignumExecM emptyRegistry
              (S2NBignumSSA.BignumModP25519_4.body.take 5))
      (fun s => ⌜s.regs "ap" = BitVec.ofNat 64 base_a.toNat ∧
                 load64Mem s.mem base_a = some a0 ∧
                 load64Mem s.mem (base_a + 8) = some a1 ∧
                 load64Mem s.mem (base_a + 16) = some a2 ∧
                 load64Mem s.mem (base_a + 24) = some a3⌝)
      (⇓? _ => fun s => ⌜s.regs "zero" = 0 ∧ s.regs "a0" = a0.toBitVec ∧
                         s.regs "a1" = a1.toBitVec ∧ s.regs "a2" = a2.toBitVec ∧
                         s.regs "a3" = a3.toBitVec⌝) := by
  show Triple (bignumExecM emptyRegistry _) _ _
  simp only [S2NBignumSSA.BignumModP25519_4.body, List.take]
  mvcgen' [bignumExecM_cons, bignumExecM_nil]
  rename_i s hpre
  obtain ⟨h_ap, h_a0, h_a1, h_a2, h_a3⟩ := hpre
  have e0 : stepAddr (stepConst s "zero" 0) "ap" 0 = base_a := by
    rw [stepAddr_of_regs (stepConst s "zero" 0) "ap" base_a 0 h_ap]; simp
  have m0 : (stepConst s "zero" 0).mem = s.mem := rfl
  simp only [m0, e0, h_a0]
  simp only [bignumExecM_cons]
  mspec stepInstrM_load64_spec
  have e1 : stepAddr (stepLoad (stepConst s "zero" 0) "a0" a0) "ap" 8 = base_a + 8 := by
    rw [stepAddr_of_regs (stepLoad (stepConst s "zero" 0) "a0" a0) "ap" base_a 8 h_ap]
    simp
  have m1 : (stepLoad (stepConst s "zero" 0) "a0" a0).mem = s.mem := rfl
  simp only [m1, e1, h_a1]
  mspec stepInstrM_load64_spec
  have e2 : stepAddr (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0) "a1" a1)
      "ap" 16 = base_a + 16 := by
    rw [stepAddr_of_regs (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0) "a1" a1)
          "ap" base_a 16 h_ap]
    simp
  have m2 : (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0) "a1" a1).mem = s.mem := rfl
  simp only [m2, e2, h_a2]
  mspec stepInstrM_load64_spec
  have e3 : stepAddr (stepLoad (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0)
      "a1" a1) "a2" a2) "ap" 24 = base_a + 24 := by
    rw [stepAddr_of_regs (stepLoad (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0)
          "a1" a1) "a2" a2) "ap" base_a 24 h_ap]
    simp
  have m3 : (stepLoad (stepLoad (stepLoad (stepConst s "zero" 0) "a0" a0)
      "a1" a1) "a2" a2).mem = s.mem := rfl
  simp only [m3, e3, h_a3, bignumExecM_nil]
  mvcgen'
  simp only [stepConst, stepLoad, setReg]
  intro _
  simp

end CatCrypt.Crypto.Jasmin.BignumHoare.MVCGenPrimeSmoke
