/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf

/-!
# Faithful `lsem` for the AVX-512 packed-lane SIMD fragment
# — increment 10 of porting jasmin's `lsem`

Increments 1–9 brought `regArith`, `regConst`, the width-mixing `select`, the
immediate shifts, the widening-multiply / carry-chain trio, the width cast
`castW`, and the opaque external leaf `extCall` into the unconditional
functional ∧ constant-time `lsem` simulation. Each of those increments named
`vpackZMM` on its deferral list as one of the remaining "SIMD axes", with the
same concrete obstruction:

> **`vpackZMM bop` (`[.reg 512, .reg 512] → .reg 512`)** — needs the SIMD lane
> model: its denotation `zmmPackQ bop a b` is the per-64-bit-lane `bop` over
> eight lanes of a 512-bit register; no scalar `lsemStep*` arm models the lane
> decomposition / `zmmPackQ` data effect.

This module **adds the `vpackZMM` arm** — faithfully, *without* a wire change.

## The SIMD lane model: a `.reg 512` value is 8 × u64 lanes

The width-tagged store `LstateN` already carries a `BitVec 512` register tag
(its `lvm` maps a name to a `Σ w, BitVec w`), so a ZMM register is held verbatim
as a `BitVec 512` value. The lane structure is *not* a new state axis: the
per-lane op `zmmPackQ bop a b = zmmOfLanes (fun k => bop.apply (zmmLane a k)
(zmmLane b k))` is a **pure `BitVec 512 → BitVec 512 → BitVec 512` data effect**
applied at the binding, exactly as `mulHiW` is for `mulhi`. The step reads the
two 512-bit sources `a, b` (at the recovered width 512, from the store tags) and
writes `zmmPackQ bop a b = (vpackZMM bop).denote …`. This is **faithful to
`eval_instr`'s `Lopn`**: evaluate the two sources, run the `#VPADD_8u64` /
`#VPSUB_8u64` / `#VPMULL_8u64` packed-lane `exec_sopn` data effect, write the
destination, advance the pc.

## The fidelity route: a typed step over the REAL `"VPACK8u64:bop"` wire form

`opToLinstrR` (`JasminLprogExport.lean:340`) lowers `vpackZMM bop` to the **bare**
mnemonic `"VPACK8u64:" ++ binOpName bop` over the two `.reg 512` sources
(no `withWidthTag`, no extra operand). The emitted bytes are exactly this. We do
**not** invent a mnemonic, add an operand, or touch the emit path. The `bop`
the lane op needs is **not** a register value; it is part of the *opcode the
binding plays* — jasmin's own `eval_instr` reads the lane operation from the
sopn descriptor (`Oasm (BaseOp (None, VPADD/VPSUB/VPMULL …))`), not from operand
syntax — so we mirror that exactly: the SIMD step is **indexed by the descriptor
`SimdDesc.vpack bop`**, recovered from the `Com` binding's typing
(`Expr.op = .vpackZMM bop`), while it runs over the REAL emitted
`"VPACK8u64:bop"` instruction. The descriptor lives only in the typed
environment (the model's `.snd` component), never on the wire, so the bytes are
unchanged (`straightOpsSimd_wire`).

Concretely, the simulation threads a list of **typed instructions** `LinstrRS :=
LinstrR × SimdDesc`, where `SimdDesc` widens increment 8/9's `Option Nat`
descriptor to carry either a cast/leaf result width (`SimdDesc.width w'`) or the
SIMD lane op (`SimdDesc.vpack bop`). The `LinstrR` component is *exactly*
`straightOpsMC`'s emitted instruction (its `.fst`-projection equals
`straightOpsMC`, the **wire/byte tie** `straightOpsSimd_wire`); every non-SIMD
binding delegates its wire and (projected) descriptor to increment 9's
`lsemStepLeaf` via the descriptor projection `SimdDesc.toOptNat`.

## Trocq (`Related`) where it helps

As in increments 6–9, the per-op denotation equality is a *representation* fact:
the value the typed SIMD step computes (read the two sources at width 512, run
`zmmPackQ bop`) realizes the abstract dialect denotation. The realization is
**definitional** — the step writes exactly `zmmPackQ bop a b`, which *is* the
`vpackZMM` `.denote` arm — so the square is `rfl`, registered as a
`Trocq.Related` identity-encoding witness (`relatedZmmPackQ`) for symmetry with
`relatedMulHi` / `relatedCastW`.

## Leakage (constant-time): the ABI, never values, and lane-obliviousness

The leak of the vpack wire `Lopn [.reg dst] ("VPACK8u64:" ++ binOpName bop)
[.reg a, .reg b]` is, by `linstrLeak`, the single event `LLeak.opn
("VPACK8u64:" ++ binOpName bop) [regShape dst] [regShape a, regShape b]` — the
opcode (which *names* the lane op `bop`, a compile-time constant) plus the
destination/source register **names** (the ABI structure), and **no register
value**. The packed-lane op `zmmPackQ bop` is **data-oblivious**: it applies the
same `bop` to every lane with no data-dependent control or addressing, so the
leak depends only on the emitted instruction (operand structure), never on a
lane value. This is automatic — `lsemLeakSimd` leaks `linstrLeak i.fst`, and the
vpack wire is an `Lopn`.

## Op set now covered

`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
addCarryHi ∪ castW ∪ extCall ∪ vpackZMM` — the `ScalarSimdN` predicate, which
subsumes increment 9's `ScalarLeafN` (`ScalarSimdN.of_scalarLeafN`). `vpackZMM`
is the **first SIMD / packed-lane op**: input two `BitVec 512`, output a
`BitVec 512`, the lane op selected by `bop`.

**All goals closed, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemLeaf
open Transfer (Related)

/-! ## 1. The realizer and its `Trocq.Related` square

The typed SIMD step's value `zmmPackQ bop a b` is exactly the dialect's
`vpackZMM` denotation, so the representation square is `rfl`; we register it as a
`Related` identity-encoding witness for symmetry with increments 7–9. The carrier
is `BitVec 512` — the first SIMD-width realizer. -/

/-- **Representation square (VPACK8u64).** The typed SIMD realizer `zmmPackQ bop a
    b` equals the dialect's `vpackZMM` denotation (definitionally — the step writes
    exactly `zmmPackQ bop a b`). Registered as a `Related` identity-encoding
    witness, the increment's analogue of `relatedMulHi` / `relatedCastW`. -/
instance relatedZmmPackQ (bop : JasminBinOp) (a b : BitVec 512) :
    Related (id : BitVec 512 → BitVec 512) (zmmPackQ bop a b) (zmmPackQ bop a b) where
  rel := rfl

/-! ## 2. The typed instruction list and its wire projection

The simulation threads `LinstrRS := LinstrR × SimdDesc`: the `LinstrR` is the
emitted instruction (`opToLinstrR`'s image, byte-for-byte), and the `SimdDesc`
carries either a cast/leaf result width (`.width w'`) or the SIMD lane op
(`.vpack bop`) — or `.none`. The `.fst`-projection of the typed list is *exactly*
`straightOpsMC` (the wire/byte tie, `straightOpsSimd_wire` below). -/

/-- The typed-step descriptor for the SIMD fragment. Widens increment 8/9's
    `Option Nat` (cast / leaf result width) to also carry the SIMD lane op `bop`
    for a `vpackZMM` binding. It is the model's typed environment — the lane op
    / result width jasmin's `exec_sopn` reads from the sopn descriptor; it never
    enters the emitted bytes (`straightOpsSimd_wire`). -/
inductive SimdDesc where
  /-- No descriptor (`regArith`/`select`/shift/trio binding). -/
  | none
  /-- A cast/leaf result width `w'` (`castW`/`extCall` binding). -/
  | width (w' : Nat)
  /-- The packed-lane op `bop` of a `vpackZMM` binding. -/
  | vpack (bop : JasminBinOp)
  deriving DecidableEq

/-- Project a `SimdDesc` to increment 9's `Option Nat` descriptor: the cast/leaf
    width passes through, and `.none`/`.vpack` map to `none` (a vpack binding is
    never delegated to `lsemStepLeaf` — the SIMD step handles it directly). The
    bridge that lets every non-SIMD head reuse the increment-9 `lsemStepLeaf`. -/
def SimdDesc.toOptNat : SimdDesc → Option Nat
  | .none => Option.none
  | .width w' => some w'
  | .vpack _ => Option.none

/-- A typed linear instruction: the emitted `LinstrR` paired with a `SimdDesc`. -/
abbrev LinstrRS : Type := LinstrR × SimdDesc

/-- Recognise a structured `"VPACK8u64:…"` packed-lane instruction `Lopn [.reg
    dst] opn [.reg a, .reg b]` (the real `vpackZMM` wire form) and return
    `(dst, a, b)`; `none` otherwise. The mnemonic is the BARE `"VPACK8u64:" ++
    binOpName bop` (`opToLinstrR` applies no `withWidthTag`), so we match the
    `"VPACK8u64:"` prefix on the character lists (which kernel-reduces on string
    literals, like `loadSymTarget?`). The `bop` itself is read from the typed
    descriptor, not parsed from the mnemonic. -/
def vpackStruct? : LinstrR → Option (String × String × String)
  | .Lopn [.reg dst] opn [.reg a, .reg b] =>
      let pfx := "VPACK8u64:".toList
      let ns := opn.toList
      if pfx.isPrefixOf ns then some (dst, a, b) else none
  | _ => none

/-- The typed single-step semantics for the SIMD fragment. On a vpack-tagged
    instruction (`vpackStruct?` recognises the `"VPACK8u64:…"` wire form *and* the
    descriptor `.vpack bop` is present) it reads the two sources `a, b` at width
    512 (`a` via `readReg`, recovering the width 512 from its store tag; `b` via
    `getW b wₐ`), and writes `zmmPackQ bop a b = (vpackZMM bop).denote …` to `dst`
    — faithful to `eval_instr`'s packed-lane `Oasm` `Lopn`. On every other typed
    instruction it delegates the wire to increment 9's `lsemStepLeaf`, with the
    descriptor projected to its `Option Nat` form (`SimdDesc.toOptNat`).

    The lane op `bop` is not on the wire; it lives only in the typed `.snd`
    descriptor (`SimdDesc.vpack bop`) — the model's typed environment, the lane op
    jasmin reads from the sopn descriptor — never a wire annotation, so the bytes
    are unchanged (`straightOpsSimd_wire`). -/
def lsemStepSimd (leaf : LeafEnvN) (i : LinstrRS) (s : LstateN) : Option LstateN :=
  match vpackStruct? i.fst, i.snd with
  | some (dst, a, b), .vpack bop =>
      match s.getW a 512, s.getW b 512 with
      | some va, some vb => some ((s.setReg dst (zmmPackQ bop va vb)).nextPc)
      | _, _ => none
  | _, _ => lsemStepLeaf leaf (i.fst, i.snd.toOptNat) s

/-- On a typed instruction whose wire is recognised by *no* vpack head (or whose
    descriptor is not `.vpack`), `lsemStepSimd` is exactly increment 9's
    `lsemStepLeaf` over the wire and the projected descriptor. (So the
    increments-1–9 steps transfer unchanged.) -/
theorem lsemStepSimd_of_delegate (leaf : LeafEnvN) (i : LinstrRS) (s : LstateN)
    (h : vpackStruct? i.fst = none ∨ (∀ bop, i.snd ≠ .vpack bop)) :
    lsemStepSimd leaf i s = lsemStepLeaf leaf (i.fst, i.snd.toOptNat) s := by
  rcases h with h | h
  · simp only [lsemStepSimd, h]
  · simp only [lsemStepSimd]
    cases hv : vpackStruct? i.fst with
    | none => rfl
    | some t =>
      cases hd : i.snd with
      | vpack bop => exact absurd hd (h bop)
      | none => rfl
      | width w' => rfl

/-! ### `lsemStraightSimd` / leakage over the typed step -/

/-- Typed straight-line execution: the sequential fold of `lsemStepSimd`. -/
def lsemStraightSimd (leaf : LeafEnvN) : List LinstrRS → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepSimd leaf i s with
      | some s' => lsemStraightSimd leaf is s'
      | none => none

@[simp] theorem lsemStraightSimd_nil (leaf : LeafEnvN) (s : LstateN) :
    lsemStraightSimd leaf [] s = some s := rfl

@[simp] theorem lsemStraightSimd_cons (leaf : LeafEnvN) (i : LinstrRS)
    (is : List LinstrRS) (s : LstateN) :
    lsemStraightSimd leaf (i :: is) s =
      (match lsemStepSimd leaf i s with
        | some s' => lsemStraightSimd leaf is s'
        | none => none) := rfl

/-- Typed leakage trace: the leak of each typed instruction is the leak of its
    **wire** (`linstrLeak i.fst`), so neither the descriptor (`.width`/`.vpack`)
    nor any lane value enters the attacker's view. For a vpack wire `Lopn [.reg
    dst] ("VPACK8u64:" ++ binOpName bop) [.reg a, .reg b]`, `linstrLeak` yields the
    opcode (which names the lane op `bop`) plus the destination/source register
    **names** (the ABI), never a value. -/
def lsemLeakSimd (leaf : LeafEnvN) : List LinstrRS → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepSimd leaf i s with
          | some s' => lsemLeakSimd leaf is s'
          | none => [])

@[simp] theorem lsemLeakSimd_nil (leaf : LeafEnvN) (s : LstateN) :
    lsemLeakSimd leaf [] s = [] := rfl

@[simp] theorem lsemLeakSimd_cons (leaf : LeafEnvN) (i : LinstrRS)
    (is : List LinstrRS) (s : LstateN) :
    lsemLeakSimd leaf (i :: is) s =
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepSimd leaf i s with
          | some s' => lsemLeakSimd leaf is s'
          | none => []) := rfl

/-! ## 3. Recognizer facts: the vpack head and the increments-1–9 images are disjoint

`vpackStruct?` recognises the real `vpackZMM` wire form; it is `none` on every
`opToLinstrR` image of the increments-1–9 heads (distinct mnemonics: none of them
starts with the `"VPACK8u64:"` prefix). With the descriptor a `.width`/`.none`
on those, `lsemStepSimd` delegates them to `lsemStepLeaf`. -/

/-- `vpackStruct?` recognises the real `vpackZMM` wire form. -/
theorem vpackStruct?_vpackZMM (bop : JasminBinOp) (dst a b : String) :
    vpackStruct? (opToLinstrR (JasminOp.vpackZMM bop) dst [.reg a, .reg b])
      = some (dst, a, b) := by
  simp only [opToLinstrR, vpackStruct?]
  rw [String.toList_append]
  simp [List.isPrefixOf]

/-! ## 4. The typed emission `straightOpsSimd` and the wire/byte tie -/

/-- The typed straight-line `LinstrRS` chain a `Com` emits in the SIMD fragment.
    The `vpackZMM` binding emits its **real** `opToLinstrR (vpackZMM bop)`
    instruction (bare `"VPACK8u64:bop"`) paired with the descriptor `.vpack bop`;
    every other binding reuses `straightOpsLeaf`'s emission, with its `Option Nat`
    descriptor re-tagged through `SimdDesc` (`none ↦ .none`, `some w' ↦ .width
    w'`). -/
def straightOpsSimd (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRS
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let elem : LinstrRS :=
        match e.op with
        | .vpackZMM bop => (opToLinstrR e.op (regName curDepth) src, .vpack bop)
        | .extCall _ _ (.reg w') => (opToLinstrR e.op (regName curDepth) src, .width w')
        | .castW _ w' => (opToLinstrR e.op (regName curDepth) src, .width w')
        | _ =>
          let wire : LinstrR :=
            match e.op, src with
            | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
            | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
            | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
            | _, _ => opToLinstrR e.op (regName curDepth) src
          (wire, .none)
      elem :: straightOpsSimd nArgs body (curDepth + 1)

/-- **The wire/byte tie.** The `.fst`-projection (the emitted bytes) of the typed
    chain `straightOpsSimd` is *exactly* increment 7's `straightOpsMC` — the
    descriptors (`.width`/`.vpack`) live only in the `.snd` component. So
    `straightOpsSimd` emits the same bytes as `straightOpsMC`, which is
    `comToBody`'s body; the vpack's wire is the REAL bare `"VPACK8u64:bop"`
    `opToLinstrR` output. -/
theorem straightOpsSimd_wire (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsSimd nArgs com curDepth).map Prod.fst =
      straightOpsMC nArgs com curDepth := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsSimd, straightOpsMC, List.map_cons, ih]
      congr 1
      cases hop : e.op <;> (try rfl)
      · rename_i name argTys retTy
        cases retTy <;> rfl

/-- The `.fst`-projection of `straightOpsSimd` also equals `straightOpsLeaf`'s
    (both project to `straightOpsMC`) — so the SIMD chain emits the same bytes as
    the increment-9 chain. -/
theorem straightOpsSimd_wire_leaf (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsSimd nArgs com curDepth).map Prod.fst =
      (straightOpsLeaf nArgs com curDepth).map Prod.fst := by
  rw [straightOpsSimd_wire, straightOpsLeaf_wire]

/-! ### `straightOpsSimd` unfolding on the vpack and delegated heads -/

theorem straightOpsSimd_vpack {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.vpackZMM bop) = .reg 512)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.vpackZMM bop)))
    (body : Com jasminDialect (.reg 512 :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.vpackZMM bop, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.vpackZMM bop) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.vpackZMM bop, heq, args⟩ : Expr jasminDialect Γ (.reg 512))), .vpack bop)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsSimd_ext {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat} (name : String)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
            Expr jasminDialect Γ (.reg w'))), .width w')
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsSimd_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.castW w w', heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.castW w w') (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), .width w')
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsSimd_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsSimd_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsSimd_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsSimd_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsSimd_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

theorem straightOpsSimd_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsSimd_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsSimd_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsSimd_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsSimd nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), .none)
      :: straightOpsSimd nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 5. Per-binding agreement for `vpackZMM` and the delegated heads -/

/-- The `exprArgs` of a `vpackZMM` binding is its two resolved 512-bit sources. -/
theorem exprArgs_vpack {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.vpackZMM bop) = .reg 512)
    (a b : Ctxt.Var Γ (.reg 512)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.vpackZMM bop, heq, .cons a (.cons b .nil)⟩ : Expr jasminDialect Γ (.reg 512))
      = [resolveVar curDepth nArgs argName (fun _ => none) a,
         resolveVar curDepth nArgs argName (fun _ => none) b] := rfl

/-- **`vpackZMM` per-binding step (packed-lane SIMD).** From a store agreeing with
    `V`, the typed vpack instruction `(opToLinstrR (vpackZMM bop) …, .vpack bop)`
    `lsemStepSimd`s to the state writing the binding's denotation
    `(vpackZMM bop).denote V = zmmPackQ bop (a.lookup V) (b.lookup V)` to
    `regName curDepth`, reading both 512-bit sources at the recovered width 512.
    Faithful to `eval_instr`'s packed-lane `Oasm` `Lopn`; the denotation equality
    is the (`rfl`) `Related` square `relatedZmmPackQ`. -/
theorem lsemStepSimd_vpack {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.vpackZMM bop) = .reg 512)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.vpackZMM bop)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.vpackZMM bop) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.vpackZMM bop, heq, args⟩ : Expr jasminDialect Γ (.reg 512))), .vpack bop)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.vpackZMM bop, heq, args⟩ : Expr jasminDialect Γ (.reg 512)).denote V)).nextPc) := by
  match args with
  | .cons a (.cons b .nil) =>
    have ha : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)) 512
        = some (a.lookup V) := by
      have := hagree a; rwa [evalOperandN_resolveVar] at this
    have hb : st.getW (operandName (resolveVar curDepth nArgs argName (fun _ => none) b)) 512
        = some (b.lookup V) := by
      have := hagree b; rwa [evalOperandN_resolveVar] at this
    rw [exprArgs_vpack bop heq a b, resolveVar_isReg a, resolveVar_isReg b]
    simp only [lsemStepSimd, vpackStruct?_vpackZMM, ha, hb]
    rfl

/-- The delegated (non-vpack) bindings step via `lsemStepSimd` to their
    denotations: each packages through `lsemStepSimd_of_delegate` then the
    increment-9 `lsemStepLeaf_*`. The vpack head is excluded (its descriptor is
    `.vpack bop` and `vpackStruct?` recognises it), so the delegate condition uses
    the non-vpack heads' descriptor / wire shape. -/
theorem lsemStepSimd_ext {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat} (name : String)
    (hname : loadSymTarget? name = none)
    (heq : DialectSignature.ret (d := jasminDialect)
      (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.extCall name [.reg w] (.reg w')) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
              Expr jasminDialect Γ (.reg w'))), .width w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ :
          Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro bop; simp))]
  exact lsemStepLeaf_ext hleaf name hname heq args hagree

theorem lsemStepSimd_cast {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.castW w w') (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), .width w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro bop; simp))]
  exact lsemStepLeaf_cast heq args hagree

theorem lsemStepSimd_var {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_var bop heq args hagree

theorem lsemStepSimd_const {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_const (V := V) n hwn heq args hagree

theorem lsemStepSimd_sel {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_sel heq args hagree

theorem lsemStepSimd_shr {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, .none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_shr hn heq args hagree

theorem lsemStepSimd_shl {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, .none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_shl hn heq args hagree

theorem lsemStepSimd_sar {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, .none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_sar hn heq args hagree

theorem lsemStepSimd_mulhi {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_mulhi heq args hagree

theorem lsemStepSimd_addLo {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_addLo heq args hagree

theorem lsemStepSimd_addHi {leaf : LeafEnvN} {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSimd leaf
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), .none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) := by
  rw [lsemStepSimd_of_delegate _ _ _ (Or.inr (by intro b; simp))]
  exact lsemStepLeaf_addHi heq args hagree

/-! ## 6. The SIMD source fragment `ScalarSimdN` -/

/-- The straight-line **SIMD-fragment** scalar source: every binding is one of the
    increment-9 opaque-leaf-fragment heads (`regArith`, `select`, an in-range
    immediate shift, the widening-multiply / carry-chain trio, a width cast, or an
    opaque external leaf), or a packed-lane `vpackZMM bop` (two `.reg 512` sources,
    `.reg 512` result). This subsumes increment 9's `ScalarLeafN`. -/
inductive ScalarSimdN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarSimdN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.castW w w', heq, args⟩ body)
  | ext {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat} (name : String)
      (hname : loadSymTarget? name = none)
      (heq : DialectSignature.ret (d := jasminDialect)
        (JasminOp.extCall name [.reg w] (.reg w')) = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.extCall name [.reg w] (.reg w'))))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.extCall name [.reg w] (.reg w'), heq, args⟩ body)
  | vpack {Γ : Ctxt jasminDialect} {s : JasminTy} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.vpackZMM bop) = .reg 512)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.vpackZMM bop)))
      {body : Com jasminDialect (.reg 512 :: Γ) s}
      (hbody : ScalarSimdN body) :
      ScalarSimdN (.var ⟨JasminOp.vpackZMM bop, heq, args⟩ body)

/-- `ScalarSimdN` subsumes `ScalarLeafN`: every increment-9 opaque-leaf-fragment
    program is in the SIMD fragment. So the increment-9 results are special
    cases. -/
theorem ScalarSimdN.of_scalarLeafN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarLeafN com) : ScalarSimdN com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih
  | const n hwn heq args _ ih => exact .const n hwn heq args ih
  | sel heq args _ ih => exact .sel heq args ih
  | shr hn heq args _ ih => exact .shr hn heq args ih
  | shl hn heq args _ ih => exact .shl hn heq args ih
  | sar hn heq args _ ih => exact .sar hn heq args ih
  | mulhi heq args _ ih => exact .mulhi heq args ih
  | addLo heq args _ ih => exact .addLo heq args ih
  | addHi heq args _ ih => exact .addHi heq args ih
  | cast heq args _ ih => exact .cast heq args ih
  | ext name hname heq args _ ih => exact .ext name hname heq args ih

/-- A `ScalarSimdN` program returns a register. -/
theorem ScalarSimdN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) : ∃ w, t = .reg w := by
  induction hcom with
  | ret v => exact ⟨_, rfl⟩
  | var _ _ _ _ ih => exact ih
  | const _ _ _ _ _ ih => exact ih
  | sel _ _ _ ih => exact ih
  | shr _ _ _ _ ih => exact ih
  | shl _ _ _ _ ih => exact ih
  | sar _ _ _ _ ih => exact ih
  | mulhi _ _ _ ih => exact ih
  | addLo _ _ _ ih => exact ih
  | addHi _ _ _ ih => exact ih
  | cast _ _ _ ih => exact ih
  | ext _ _ _ _ _ ih => exact ih
  | vpack _ _ _ _ ih => exact ih

/-! ## 7. The core SIMD straight-line simulation -/

/-- **Core simulation (parametrized by an agreeing start state), SIMD fragment,
    under the carried leaf agreement `LeafAgreesN leaf`.** From any width-tagged
    store `st` agreeing with `V` at depth `curDepth`, running the SIMD-fragment
    `.var`-chain `straightOpsSimd` succeeds, lands in a store agreeing with the
    binding-extended valuation, and reads `Com.denote com V` (transported to its
    return width) at the return register. The `vpackZMM` binding's value is
    `zmmPackQ bop`, tied to the dialect denotation by `relatedZmmPackQ` (`rfl`). -/
theorem lsemStraightSimd_straightOps {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightSimd leaf (straightOpsSimd nArgs com curDepth) st = some st' ∧
        evalOperandN st' w (.reg (comRetReg nArgs argName com curDepth)) =
          some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  induction hcom with
  | ret v =>
      intro nArgs curDepth st V w hw hlen harg hagree
      cases hw
      refine ⟨st, rfl, ?_⟩
      have key : resolveVar curDepth nArgs argName (fun _ => none) v
          = LOperand.reg (comRetReg nArgs argName (Com.ret v) curDepth) := by
        simp only [comRetReg, resolveVar]
        split <;> rfl
      rw [← key]
      exact hagree v
  | var bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_var (leaf := leaf) (V := V) (st := st) bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_var, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_const (leaf := leaf) (V := V) (st := st) n hwn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_const, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_sel (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_sel, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_shr (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_shr, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_shl (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_shl, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_sar (leaf := leaf) (V := V) (st := st) hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_sar, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_mulhi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_mulhi, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_addLo (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_addLo, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_addHi (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_addHi, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | cast heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_cast (leaf := leaf) (V := V) (st := st) heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_cast, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_ext hleaf (V := V) (st := st) name hname heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.extCall name _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_ext, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | vpack bop heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSimd_vpack (leaf := leaf) (V := V) (st := st) bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.vpackZMM bop, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsSimd_vpack, lsemStraightSimd_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 8. Faithfulness, leak state-independence, and the capstone -/

/-- **Straight-line linearizer simulation, SIMD fragment.** -/
theorem comToLprog_lsemSimd {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightSimd_straightOps hleaf hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), SIMD fragment.** -/
theorem comToLprog_faithful_simd {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemSimd hleaf hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, SIMD fragment (unconditional in the input
    valuations).** The leakage trace of the SIMD-fragment `.var`-chain is the
    **same from any two initial states agreeing with the same valuation**: every
    head (the increment-9 heads, or a `vpackZMM`) has a `linstrLeak` reading only
    the wire syntax — for `vpackZMM`, the opcode (which names the lane op `bop`)
    and the source/destination register *names* (the ABI), never a lane value, the
    descriptor, nor the packed result — and `lsemStepSimd`s successfully, so both
    states take the `some` branch and the tails (still agreeing with the extended
    valuation) close by the IH. The packed-lane op is data-oblivious. -/
theorem lsemLeakSimd_straightOps_state_independent {leaf : LeafEnvN}
    (hleaf : LeafAgreesN leaf) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakSimd leaf (straightOpsSimd nArgs com curDepth) s₁ =
        lsemLeakSimd leaf (straightOpsSimd nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_var (leaf := leaf) (V := V₁) bop heq args hag1
      have hstep2 := lsemStepSimd_var (leaf := leaf) (V := V₂) bop heq args hag2
      rw [straightOpsSimd_var]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_const (leaf := leaf) (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepSimd_const (leaf := leaf) (V := V₂) n hwn heq args hag2
      rw [straightOpsSimd_const]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_sel (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepSimd_sel (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsSimd_sel]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_shr (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSimd_shr (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsSimd_shr]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_shl (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSimd_shl (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsSimd_shl]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_sar (leaf := leaf) (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSimd_sar (leaf := leaf) (V := V₂) hn heq args hag2
      rw [straightOpsSimd_sar]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_mulhi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepSimd_mulhi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsSimd_mulhi]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_addLo (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepSimd_addLo (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsSimd_addLo]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_addHi (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepSimd_addHi (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsSimd_addHi]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | cast heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_cast (leaf := leaf) (V := V₁) heq args hag1
      have hstep2 := lsemStepSimd_cast (leaf := leaf) (V := V₂) heq args hag2
      rw [straightOpsSimd_cast]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | ext name hname heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_ext hleaf (V := V₁) name hname heq args hag1
      have hstep2 := lsemStepSimd_ext hleaf (V := V₂) name hname heq args hag2
      rw [straightOpsSimd_ext]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | vpack bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSimd_vpack (leaf := leaf) (V := V₁) bop heq args hag1
      have hstep2 := lsemStepSimd_vpack (leaf := leaf) (V := V₂) bop heq args hag2
      rw [straightOpsSimd_vpack]
      simp only [lsemLeakSimd_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 9. The unconditional SIMD capstone: `correct ∧ robust` -/

/-- **`correct ∧ robust` for the SIMD fragment
    (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
    addCarryHi ∪ castW ∪ extCall ∪ vpackZMM`), under the carried leaf agreement.**
    For a SIMD-fragment scalar straight-line `Com` with return type `.reg w` and a
    leaf environment `leaf` whose external primitives agree with the dialect
    (`LeafAgreesN leaf`):

    1. *(correct, §7/8)* running the linearizer-emitted `.var`-chain
       `straightOpsSimd` on the encoded argument valuation and decoding the result
       register at width `w` yields exactly `com.denote V`; and
    2. *(robust, syntactic leak model, §8)* the leakage trace `lsemLeakSimd
       (straightOpsSimd …)` is the **same from the encodings of any two input
       valuations** — the attacker's view is a function of the emitted instruction
       list alone, never of a register value, the descriptor, or the packed-lane
       result. For a `vpackZMM` it leaks the opcode (which names the lane op `bop`)
       + source-register **structure** (the ABI), never lane values; the packed-
       lane op is data-oblivious.

    This is **unconditional in the runtime inputs**: no IR→x86 faithfulness
    hypothesis, no `jasminc_preserves_ct`. The **only** carried hypothesis is
    `LeafAgreesN leaf` — the external primitive's own KAT (carried since increment
    9 for `extCall`; `vpackZMM` adds no new hypothesis: its lane op is a verified
    dialect denotation). Both conjuncts concern one and the same object — the
    SIMD linearizer-emitted straight-line body run by `lsemStraightSimd`
    (functional) and observed by `lsemLeakSimd` (CT). The packed op is read over
    the REAL bare `"VPACK8u64:bop"` `opToLinstrR` already emits
    (`straightOpsSimd_wire`: the `.fst`-projection is exactly `straightOpsMC`), so
    the emitted **bytes are unchanged**; the lane op `bop` is the typed-step
    descriptor, never a wire annotation. The `lsem→bytes` encoder and Sail tables
    remain the declared trusted base.

    The leak function reads no register value (an indexed access leaks the index
    register's name, not its value), so conjunct 2 holds for every program of the
    fragment and is not constant-time evidence. Constant-time evidence for emitted
    code is `AllocCTPreservation.toLprogPhysAbi_gather_constant_time` (straight-line
    gathered blocks) and the per-kernel `blockLeak` theorems. -/
theorem owned_lsem_correct_and_robust_simd {leaf : LeafEnvN} (hleaf : LeafAgreesN leaf)
    {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarSimdN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§7/8), under the carried leaf agreement
    ((lsemStraightSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§8)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_simd hleaf hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakSimd_straightOps_state_independent hleaf hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 10. Tie-back: the increment-9 opaque-leaf fragment is subsumed -/

/-- Every increment-9 opaque-leaf-fragment program satisfies the SIMD capstone
    (for any agreeing leaf): the increment-9 results are special cases of the
    increment-10 ones. -/
theorem owned_lsem_correct_and_robust_simd_of_scalarLeafN {leaf : LeafEnvN}
    (hleaf : LeafAgreesN leaf) {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarLeafN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakSimd leaf (straightOpsSimd Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_simd hleaf (ScalarSimdN.of_scalarLeafN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimd
