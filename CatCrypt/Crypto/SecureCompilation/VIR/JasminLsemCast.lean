/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
public import Transfer.Base.Related

/-!
# Faithful `lsem` for the width-cast fragment
# — increment 8 of porting jasmin's `lsem`

Increments 1–7 brought `regArith`, `regConst`, the width-mixing `select`, the
immediate shifts (`shrImm`/`shlImm`/`sarImm`) and the widening-multiply /
carry-chain trio (`mulhi`/`addCarryLo`/`addCarryHi`) into the unconditional
functional ∧ constant-time `lsem` simulation. Each of those increments named
`castW` on its deferral list, with the same concrete obstruction:

> **`castW w w'` (`w ≠ w'`)** — lowers to `Lopn [.reg dst] ("ZEROEXT"/"TRUNC")
> [src]`. The **output width `w'` is not recoverable** from the emitted
> `LinstrR`: the mnemonic carries no width tag … the store only tells the step
> the *input* width `w` (from `src`'s stored tag), never the target `w'`.

This module **adds the `castW` arm** — faithfully, *without* a wire change.

## The fidelity route: a typed step over the REAL `"ZEROEXT"/"TRUNC"` wire form

`opToLinstrR` lowers `castW w w'` to the **bare** mnemonic
`if w' ≥ w then "ZEROEXT" else "TRUNC"` over the single source `[src]`
(`JasminLprogExport.lean`, no `withWidthTag`, no `.imm w'` operand). The emitted
bytes are exactly this. We do **not** invent a `"CASTW"` mnemonic, nor add a
`.imm w'` operand, nor touch the emit path — the exported bytes are byte-for-byte
the increments-1–7 bytes plus this same `"ZEROEXT"/"TRUNC"` form the renderer
(`LprogAsmPrinter`, `movzbl`) already consumes.

The output width `w'` is genuinely absent from that wire. The renderer recovers
nothing from a typed environment either — it hardcodes the byte-boundary cast
(`LprogAsmPrinter` §ZEROEXT/TRUNC), so there is **no shared width-source** in the
renderer to read (route 1 is unavailable). The faithful route is the **typed
step** (route 2): jasmin's own `eval_instr` reads the cast width from the *sopn
descriptor* `Ozeroext ws' ws` — the typed instruction — **not** from the operand
syntax (`JasminPrintSemCorrect.lean`: `castW w w' ↦ Papp1 (Ozeroext ws' ws) …`).
We mirror that exactly: the cast step is **indexed by the descriptor width `w'`**,
recovered from the `Com` binding's typing (`Expr.op = .castW w w'`, whose
`DialectSignature.ret` is `.reg w'`), while it runs over the REAL emitted
`"ZEROEXT"/"TRUNC"` instruction. The descriptor is the lsem model's typed
environment — the same `ws'` jasmin's `read_linear` reconstructs from the typed
program — never a change to the surface syntax the bytes are printed from.

Concretely, the simulation threads a list of **typed instructions**
`LinstrRT := LinstrR × Option Nat`: the `LinstrR` component is *exactly*
`straightOpsMC`'s emitted instruction (its `.fst`-projection equals
`straightOpsMC`, proved below — the **wire/byte tie**), and the `Option Nat`
carries the cast descriptor `w'` for a cast binding (`none` otherwise). The step
`lsemStepCast` reads its source `a` at the recovered input width `w` (from `a`'s
store tag) and writes `(va).zeroExtend w' = (castW w w').denote …` at the
descriptor width `w'`. This is **faithful to `eval_instr`'s `Lopn`** (evaluate the
source, run the `Ozeroext` `exec_sopn` data effect at the descriptor width, write
the destination, advance pc).

## Trocq (`Related`) where it helps

As in increments 6/7, the per-op denotation equality is a *representation* fact:
the value the typed cast step computes (read the source at its store width, run
`BitVec.zeroExtend w'`) realizes the abstract dialect denotation. The realization
is **definitional** — the step writes exactly `(va).zeroExtend w'`, which *is* the
`castW` `.denote` arm — so the square is `rfl`, registered as a `Trocq.Related`
identity-encoding witness (`relatedCastW`) for symmetry with `relatedStructShr` /
`relatedMulHi`.

## Op set now covered

`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪ addCarryHi ∪
castW` — the `ScalarCastN` predicate, which subsumes increment 7's
`ScalarMulCarryN` (`ScalarCastN.of_scalarMulCarryN`). `castW` is the **third**
genuinely width-mixing op (after `select` and `addCarryHi`): input `BitVec w`,
output `BitVec w'`, in general `w ≠ w'`. Still deferred, with the same honest
reasons as increments 5–7: `regConst` (string-baked width on the wire),
`stackLoad`/`stackStore` (the memory/array carrier, an orthogonal state axis),
`vpackZMM`/`extCall`/`callN` (SIMD / opaque-leaf axes).

**0 sorries, axioms ⊆ {propext, Classical.choice, Quot.sound}, no
`jasminc_preserves_ct`.** The `lsem→bytes` encoder and Sail tables remain the
declared trusted base, as for every verified compiler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemMulCarry
open Transfer (Related)

/-! ## 1. The realizer and its `Trocq.Related` square

The typed cast step's value `(va).zeroExtend w'` is exactly the dialect's `castW`
denotation, so the representation square is `rfl`; we register it as a `Related`
identity-encoding witness for symmetry with increments 6/7. The carrier crosses
widths (`BitVec w → BitVec w'`), the first realizer whose source and target
widths genuinely differ. -/

/-- **Representation square (ZEROEXT/TRUNC).** The typed cast realizer
    `(va).zeroExtend w'` equals the dialect's `castW` denotation (definitionally —
    the step writes exactly `BitVec.zeroExtend w'`). Registered as a `Related`
    identity-encoding witness, the increment's analogue of `relatedStructShr` /
    `relatedMulHi`. Note the carrier crosses widths `BitVec w → BitVec w'`. -/
instance relatedCastW {w w' : Nat} (va : BitVec w) :
    Related (id : BitVec w' → BitVec w') (va.zeroExtend w') (va.zeroExtend w') where
  rel := rfl

/-! ## 2. The typed instruction list and its wire projection

The simulation threads `LinstrRT := LinstrR × Option Nat`: the `LinstrR` is the
emitted instruction (`opToLinstrR`'s image, byte-for-byte), and the `Option Nat`
carries the cast descriptor width `w'` for a cast binding (`none` otherwise). The
`.fst`-projection of the typed list is *exactly* `straightOpsMC` (the wire/byte
tie, `straightOpsCast_wire` below). -/

/-- A typed linear instruction: the emitted `LinstrR` paired with an optional cast
    descriptor width `w'`. The pairing carries — for the lsem model only — the
    `ws'` jasmin's `exec_sopn`/`read_linear` reads from the `Ozeroext` descriptor;
    it never enters the emitted bytes (`straightOpsCast_wire`). -/
abbrev LinstrRT : Type := LinstrR × Option Nat

/-- Recognise a structured `ZEROEXT`/`TRUNC` instruction `Lopn [.reg dst] opn
    [.reg a]` (the real `castW` wire form) and return `(dst, a)`; `none`
    otherwise. The mnemonic is the BARE `"ZEROEXT"`/`"TRUNC"` (`opToLinstrR`
    applies no `withWidthTag`), so we match it directly — no tag to strip. -/
def castStruct? : LinstrR → Option (String × String)
  | .Lopn [.reg dst] opn [.reg a] =>
      if opn = "ZEROEXT" ∨ opn = "TRUNC" then some (dst, a) else none
  | _ => none

/-- The typed single-step semantics for the width-cast fragment. On a cast-tagged
    instruction (`castStruct?` recognises the `"ZEROEXT"/"TRUNC"` wire form *and*
    the descriptor `some w'` is present) it reads the source `a` at its store
    width `w` (recovered from `a`'s tag), and writes `(va).zeroExtend w' =
    (castW w w').denote …` at the **descriptor width `w'`** — faithful to
    `eval_instr`'s `Ozeroext` `Lopn`. On every other typed instruction it
    delegates the wire to increment 7's `lsemStepMC` (the descriptor is `none`).

    The descriptor `w'` is the typed-step parameter (jasmin reads it from the
    sopn descriptor, not the operand syntax); the wire `i.fst` is the REAL emitted
    `"ZEROEXT"/"TRUNC"` instruction. -/
def lsemStepCast (i : LinstrRT) (s : LstateN) : Option LstateN :=
  match castStruct? i.fst, i.snd with
  | some (dst, a), some w' =>
      match readReg s (.reg a) with
      | some ⟨_, va⟩ => some ((s.setReg dst (va.zeroExtend w')).nextPc)
      | none => none
  | _, _ => lsemStepMC i.fst s

/-- On a typed instruction whose wire is recognised by *no* cast head (or whose
    descriptor is `none`), `lsemStepCast` is exactly increment 7's `lsemStepMC`
    over the wire. (So the increments-1–7 steps transfer unchanged.) -/
theorem lsemStepCast_of_delegate (i : LinstrRT) (s : LstateN)
    (h : castStruct? i.fst = none ∨ i.snd = none) :
    lsemStepCast i s = lsemStepMC i.fst s := by
  rcases h with h | h
  · simp only [lsemStepCast, h]
  · simp only [lsemStepCast, h]; cases castStruct? i.fst <;> rfl

/-! ### `lsemStraightCast` / leakage over the typed step -/

/-- Typed straight-line execution: the sequential fold of `lsemStepCast`. -/
def lsemStraightCast : List LinstrRT → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepCast i s with
      | some s' => lsemStraightCast is s'
      | none => none

@[simp] theorem lsemStraightCast_nil (s : LstateN) : lsemStraightCast [] s = some s := rfl

@[simp] theorem lsemStraightCast_cons (i : LinstrRT) (is : List LinstrRT) (s : LstateN) :
    lsemStraightCast (i :: is) s =
      (match lsemStepCast i s with
        | some s' => lsemStraightCast is s'
        | none => none) := rfl

/-- Typed leakage trace: the leak of each typed instruction is the leak of its
    **wire** (`linstrLeak i.fst`), so the descriptor `w'` never enters the
    attacker's view (it is the model's typed environment, not a register value).
    Faithful to the emit path: the bytes are `i.fst`, so the leak is of `i.fst`. -/
def lsemLeakCast : List LinstrRT → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepCast i s with
          | some s' => lsemLeakCast is s'
          | none => [])

@[simp] theorem lsemLeakCast_nil (s : LstateN) : lsemLeakCast [] s = [] := rfl

@[simp] theorem lsemLeakCast_cons (i : LinstrRT) (is : List LinstrRT) (s : LstateN) :
    lsemLeakCast (i :: is) s =
      JasminLsemRobust.linstrLeak i.fst ++
        (match lsemStepCast i s with
          | some s' => lsemLeakCast is s'
          | none => []) := rfl

/-! ## 3. Recognizer facts: the cast head and the increments-1–7 images are disjoint

`castStruct?` recognises the real `castW` wire form; it is `none` on every
`opToLinstrR` image of `regArith`/`select`/shifts/the trio (distinct mnemonics or
operand shapes). With the descriptor threaded as `none` on those, `lsemStepCast`
delegates them to `lsemStepMC`. -/

/-- `castStruct?` recognises the real `castW` wire form `Lopn [.reg dst]
    ("ZEROEXT"/"TRUNC") [.reg a]`. -/
theorem castStruct?_castW {w w' : Nat} (dst a : String) :
    castStruct? (opToLinstrR (JasminOp.castW w w') dst [.reg a]) = some (dst, a) := by
  simp only [opToLinstrR, castStruct?]
  split <;> simp

/-! ## 4. The typed emission `straightOpsCast` and the wire/byte tie

`straightOpsCast` mirrors increment 7's `straightOpsMC`, but emits the typed
`LinstrRT` for each binding: the cast binding emits its real `opToLinstrR`
instruction paired with the descriptor `some w'`; every other binding emits its
`straightOpsMC` instruction paired with `none`. The `.fst`-projection of the
typed list is *exactly* `straightOpsMC` — the wire/byte tie. -/

/-- The typed straight-line `LinstrRT` chain a `Com` emits in the width-cast
    fragment. The cast binding emits its **real** `opToLinstrR (castW w w')`
    instruction (bare `"ZEROEXT"/"TRUNC"`) paired with the descriptor `some w'`;
    every other binding reuses `straightOpsMC`'s emission paired with `none`. The
    `none`-descriptor instructions are passed verbatim to `lsemStepMC`. -/
def straightOpsCast (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrRT
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let elem : LinstrRT :=
        match e.op with
        | .castW _ w' => (opToLinstrR e.op (regName curDepth) src, some w')
        | _ =>
          let wire : LinstrR :=
            match e.op, src with
            | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
            | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
            | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
            | _, _ => opToLinstrR e.op (regName curDepth) src
          (wire, none)
      elem :: straightOpsCast nArgs body (curDepth + 1)

/-- **The wire/byte tie.** The `.fst`-projection (the emitted bytes) of the typed
    chain `straightOpsCast` is *exactly* increment 7's `straightOpsMC` — the cast
    descriptor `w'` lives only in the `.snd` component and never enters the wire.
    So `straightOpsCast` emits the same bytes as `straightOpsMC`, which is
    `comToBody`'s body (`straightOpsMC` / `straightOps_eq_body`) — the cast's wire
    is the REAL bare `"ZEROEXT"/"TRUNC"` `opToLinstrR` output. -/
theorem straightOpsCast_wire (nArgs : Nat) {Γ : Ctxt jasminDialect} {t : JasminTy}
    (com : Com jasminDialect Γ t) (curDepth : Nat) :
    (straightOpsCast nArgs com curDepth).map Prod.fst =
      straightOpsMC nArgs com curDepth := by
  induction com generalizing curDepth with
  | ret v => rfl
  | var e body ih =>
      simp only [straightOpsCast, straightOpsMC, List.map_cons, ih]
      congr 1
      cases e.op <;> rfl

/-! ### `straightOpsCast` unfolding on each binding head -/

theorem straightOpsCast_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (body : Com jasminDialect (.reg w' :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.castW w w', heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.castW w w') (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCast_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCast_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCast_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      (shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n, none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

theorem straightOpsCast_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsCast_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.regConst w n, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .nil => rfl

theorem straightOpsCast_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsCast_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.mulhi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

theorem straightOpsCast_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

theorem straightOpsCast_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (body : Com jasminDialect (.reg 1 :: Γ) s) :
    straightOpsCast nArgs (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body) curDepth =
      (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
      :: straightOpsCast nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 5. Per-binding agreement for `castW` and the delegated heads -/

/-- The `exprArgs` of a `castW` binding is its single resolved source. -/
theorem exprArgs_castW {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (a : Ctxt.Var Γ (.reg w)) :
    exprArgs curDepth nArgs argName (fun _ => none)
      (⟨JasminOp.castW w w', heq, .cons a .nil⟩ : Expr jasminDialect Γ (.reg w'))
      = [resolveVar curDepth nArgs argName (fun _ => none) a] := rfl

/-- **`castW` per-binding step (width-mixing cast).** From a store agreeing with
    `V`, the typed cast instruction `(opToLinstrR (castW w w') …, some w')`
    `lsemStepCast`s to the state writing the binding's denotation
    `(castW w w').denote V = (a.lookup V).zeroExtend w'` to `regName curDepth`,
    reading the source `a` at the recovered **input** width `w` and writing at the
    **descriptor** width `w'`. Faithful to `eval_instr`'s `Ozeroext` `Lopn`; the
    denotation equality is the (`rfl`) `Related` square `relatedCastW`. -/
theorem lsemStepCast_cast {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w w' : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.castW w w') (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w'))), some w')
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.castW w w', heq, args⟩ : Expr jasminDialect Γ (.reg w')).denote V)).nextPc) := by
  match args with
  | .cons a .nil =>
    have ha : readReg st (.reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) a)))
        = some ⟨w, a.lookup V⟩ := by
      have := readReg_resolveVar a hagree; rwa [resolveVar_isReg a] at this
    rw [exprArgs_castW heq a, resolveVar_isReg a]
    simp only [lsemStepCast, castStruct?_castW, ha]
    rfl

/-- The delegated (non-cast) bindings step via `lsemStepCast` to their
    denotations. We package the eight delegated heads through
    `lsemStepCast_of_delegate` (descriptor `= none`) reducing to the increment-7
    `lsemStepMC_*`. -/
theorem lsemStepCast_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_var bop heq args hagree

theorem lsemStepCast_const {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_const (V := V) n hwn heq args hagree

theorem lsemStepCast_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_sel heq args hagree

theorem lsemStepCast_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_shr hn heq args hagree

theorem lsemStepCast_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_shl hn heq args hagree

theorem lsemStepCast_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n, none) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_sar hn heq args hagree

theorem lsemStepCast_mulhi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.mulhi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.mulhi w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_mulhi heq args hagree

theorem lsemStepCast_addLo {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.addCarryLo w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryLo w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_addCarryLo heq args hagree

theorem lsemStepCast_addHi {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepCast
        (opToLinstrR (JasminOp.addCarryHi w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1))), none)
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.addCarryHi w, heq, args⟩ : Expr jasminDialect Γ (.reg 1)).denote V)).nextPc) := by
  rw [lsemStepCast_of_delegate _ _ (Or.inr rfl)]
  exact lsemStepMC_addCarryHi heq args hagree

/-! ## 6. The width-cast source fragment `ScalarCastN` -/

/-- The straight-line **width-cast-fragment** scalar source: every binding is a
    `regArith`, a width-mixing `select`, an in-range immediate shift, one of the
    widening-multiply / carry-chain trio, or a width cast `castW w w'`. This
    subsumes increment 7's `ScalarMulCarryN`. The `castW` arm binds a `.reg w'`
    (the **target** width, in general `≠` the source width `w`) into the body
    context — the first genuinely width-*changing* binder. -/
inductive ScalarCastN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarCastN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | const {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (n : Nat)
      (hwn : w = 64 ∨ w = 32)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.regConst w n, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)
  | mulhi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.mulhi w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.mulhi w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.mulhi w, heq, args⟩ body)
  | addLo {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryLo w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryLo w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.addCarryLo w, heq, args⟩ body)
  | addHi {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.addCarryHi w) = .reg 1)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.addCarryHi w)))
      {body : Com jasminDialect (.reg 1 :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.addCarryHi w, heq, args⟩ body)
  | cast {Γ : Ctxt jasminDialect} {s : JasminTy} {w w' : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.castW w w') = .reg w')
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.castW w w')))
      {body : Com jasminDialect (.reg w' :: Γ) s}
      (hbody : ScalarCastN body) :
      ScalarCastN (.var ⟨JasminOp.castW w w', heq, args⟩ body)

/-- `ScalarCastN` subsumes `ScalarMulCarryN`: every increment-7 mul/carry-fragment
    program is in the width-cast fragment. So the increment-7 results are special
    cases. -/
theorem ScalarCastN.of_scalarMulCarryN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarMulCarryN com) : ScalarCastN com := by
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

/-- A `ScalarCastN` program returns a register. -/
theorem ScalarCastN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) : ∃ w, t = .reg w := by
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

/-! ## 7. The core width-cast straight-line simulation

Same induction skeleton as increment 7's `lsemStraightMC_straightOps`, with the
new `cast` arm closed by `lsemStepCast_cast` + `StoreAgreesN.step`, and the eight
delegated arms by the `lsemStepCast_*` (each reducing to `lsemStepMC_*` through
`lsemStepCast_of_delegate`). The `cast` arm steps a `.reg w'` binding, so the
binding-extended valuation is over `.reg w' :: Γ` — `StoreAgreesN.step` is generic
over the written width, so it absorbs the width-changing cast without change. -/

/-- **Core simulation (parametrized by an agreeing start state), width-cast
    fragment.** From any width-tagged store `st` agreeing with `V` at depth
    `curDepth`, running the width-cast-fragment `.var`-chain `straightOpsCast`
    succeeds, lands in a store agreeing with the binding-extended valuation, and
    reads `Com.denote com V` (transported to its return width) at the return
    register. -/
theorem lsemStraightCast_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightCast (straightOpsCast nArgs com curDepth) st = some st' ∧
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
      have hstep := lsemStepCast_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_var, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_const (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        n hwn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regConst _ n, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_const, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_sel, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_shr (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_shr, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_shl (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_shl, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_sar (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_sar, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | mulhi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_mulhi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.mulhi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_mulhi, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addLo heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_addLo (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryLo _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_addLo, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | addHi heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_addHi (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.addCarryHi _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_addHi, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | cast heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepCast_cast (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.castW _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsCast_cast, lsemStraightCast_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 8. Faithfulness, leak state-independence, and the capstone -/

/-- **Straight-line linearizer simulation, width-cast fragment.** Running the
    width-cast-fragment `.var`-chain `straightOpsCast` from the encoded argument
    valuation and decoding the result register at width `w` equals the source
    program's `Com.denote`. -/
theorem comToLprog_lsemCast {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightCast (straightOpsCast Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightCast_straightOps hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), width-cast fragment.** -/
theorem comToLprog_faithful_cast {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightCast (straightOpsCast Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemCast hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, width-cast fragment (unconditional).** The leakage
    trace of the width-cast-fragment `.var`-chain is the **same from any two
    initial states agreeing with the same valuation**: every head (`regArith`,
    `select`, a shift, one of the trio, or a `castW`) has a `linstrLeak` reading
    only the wire syntax — for `castW`, the source register *name*, never a
    register value nor the descriptor width — and `lsemStepCast`s successfully, so
    both states take the `some` branch and the tails (still agreeing with the
    extended valuation) close by the IH. -/
theorem lsemLeakCast_straightOps_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakCast (straightOpsCast nArgs com curDepth) s₁ =
        lsemLeakCast (straightOpsCast nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_var (V := V₁) bop heq args hag1
      have hstep2 := lsemStepCast_var (V := V₂) bop heq args hag2
      rw [straightOpsCast_var]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | const n hwn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_const (V := V₁) n hwn heq args hag1
      have hstep2 := lsemStepCast_const (V := V₂) n hwn heq args hag2
      rw [straightOpsCast_const]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_sel (V := V₁) heq args hag1
      have hstep2 := lsemStepCast_sel (V := V₂) heq args hag2
      rw [straightOpsCast_sel]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_shr (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCast_shr (V := V₂) hn heq args hag2
      rw [straightOpsCast_shr]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_shl (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCast_shl (V := V₂) hn heq args hag2
      rw [straightOpsCast_shl]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_sar (V := V₁) hn heq args hag1
      have hstep2 := lsemStepCast_sar (V := V₂) hn heq args hag2
      rw [straightOpsCast_sar]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | mulhi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_mulhi (V := V₁) heq args hag1
      have hstep2 := lsemStepCast_mulhi (V := V₂) heq args hag2
      rw [straightOpsCast_mulhi]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addLo heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_addLo (V := V₁) heq args hag1
      have hstep2 := lsemStepCast_addLo (V := V₂) heq args hag2
      rw [straightOpsCast_addLo]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | addHi heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_addHi (V := V₁) heq args hag1
      have hstep2 := lsemStepCast_addHi (V := V₂) heq args hag2
      rw [straightOpsCast_addHi]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | cast heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepCast_cast (V := V₁) heq args hag1
      have hstep2 := lsemStepCast_cast (V := V₂) heq args hag2
      rw [straightOpsCast_cast]
      simp only [lsemLeakCast_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 9. The unconditional width-cast capstone: `correct ∧ robust` -/

/-- **Unconditional `correct ∧ robust` for the width-cast fragment
    (`regArith ∪ select ∪ shrImm ∪ shlImm ∪ sarImm ∪ mulhi ∪ addCarryLo ∪
    addCarryHi ∪ castW`).** For a width-cast-fragment scalar straight-line `Com`
    with return type `.reg w`:

    1. *(correct, §8)* running the linearizer-emitted `.var`-chain
       `straightOpsCast` on the encoded argument valuation and decoding the result
       register at width `w` yields exactly `com.denote V`; and
    2. *(robust / constant-time, §8)* the leakage trace `lsemLeakCast
       (straightOpsCast …)` is the **same from the encodings of any two input
       valuations** — the attacker's view is a function of the emitted instruction
       list alone, never of a register value (and never of the cast descriptor
       width `w'`, which lives only in the typed `.snd` component).

    This is **unconditional**: no IR→x86 faithfulness hypothesis, no
    `jasminc_preserves_ct`. Both conjuncts concern one and the same object — the
    width-cast linearizer-emitted straight-line body run by `lsemStraightCast`
    (functional) and observed by `lsemLeakCast` (CT). The width cast is read over
    the REAL bare role mnemonic `"ZEROEXT"/"TRUNC"` `opToLinstrR` already emits
    (`straightOpsCast_wire`: the `.fst`-projection is exactly `straightOpsMC`), so
    the emitted **bytes are unchanged**; the target width `w'` is the typed-step
    descriptor (the `ws'` jasmin's `exec_sopn` reads from the `Ozeroext` sopn),
    never a wire annotation. The first capstone covering `castW` — the **third**
    genuinely width-mixing op (after `select` and `addCarryHi`): input `BitVec w`,
    output `BitVec w'` (in general `w ≠ w'`) in one instruction. The `lsem→bytes`
    encoder and Sail tables remain the declared trusted base. -/
theorem owned_lsem_correct_and_robust_cast {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarCastN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    -- (1) functional correctness (§8)
    ((lsemStraightCast (straightOpsCast Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    -- (2) robustness / constant-time leakage (§8)
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakCast (straightOpsCast Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakCast (straightOpsCast Γ.length com Γ.length) (encodeN V₂)) := by
  refine ⟨comToLprog_faithful_cast hcom hw V, ?_⟩
  intro V₁ V₂
  exact lsemLeakCast_straightOps_state_independent hcom (encodeN V₁) (encodeN V₂)
    rfl le_rfl (encodeN_StoreAgreesN V₁) (encodeN_StoreAgreesN V₂)

/-! ## 10. Tie-back: the increment-7 mul/carry fragment is subsumed

`ScalarCastN.of_scalarMulCarryN` shows every `ScalarMulCarryN` program is a
`ScalarCastN` program. The width-cast capstone therefore specialises to the
mul/carry fragment (and, transitively, to the shift / width-mixed / `regArith`
fragments of increments 2–6). -/

/-- Every increment-7 mul/carry-fragment program satisfies the width-cast
    capstone: the increment-7 results are special cases of the increment-8 ones. -/
theorem owned_lsem_correct_and_robust_cast_of_scalarMulCarryN {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarMulCarryN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    ((lsemStraightCast (straightOpsCast Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧))
    ∧
    (∀ V₁ V₂ : Ctxt.Valuation Γ,
      lsemLeakCast (straightOpsCast Γ.length com Γ.length) (encodeN V₁) =
        lsemLeakCast (straightOpsCast Γ.length com Γ.length) (encodeN V₂)) :=
  owned_lsem_correct_and_robust_cast (ScalarCastN.of_scalarMulCarryN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemCast
