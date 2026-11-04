/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
public import CatCrypt.Crypto.SecureCompilation.VIR.SarCount
public import Transfer.Base.Related

/-!
# The `lsem` functional simulation for the immediate-shift fragment

The `lsem` functional simulation covers `regArith`, `regConst` and the
width-mixing `select` (`JasminLsemScalar`, `JasminLsemWidthN`). The immediate
shifts `shrImm`/`shlImm`/`sarImm`/`rorImm` carry an obstruction recorded in
`JasminLsemScalar.lean §"Immediate baked into the opcode mnemonic"`:

> `opToLinstrR` encodes the shift amount **in the opcode string**
> (`withWidthTag w ("SHR:" ++ toString n)`), *not* in an operand. A faithful
> `lsemStep` … would have to recover `n` by parsing `toString n` back out of the
> mnemonic — i.e. `(toString n).toNat? = some n`, which has **no Lean/Mathlib
> round-trip lemma** and is **not** closable by `decide` for symbolic `n`.

This module closes that gap by the **wire-format redesign** the task authorises:
make the shift amount *structurally recoverable* — carry it in an `.imm`
**operand**, exactly as `regConst` already does for its constant, exactly as the
downstream `legalizeShiftImmLprog` pass already rewrites the unary `SHR:<n>:64`
into the two-source operand form `[d] SHR:64 [d, #n]` before byte rendering.

## The structured shift instruction (route (a): the byte-rendered form)

For a `shrImm w n` (resp. `shlImm`/`sarImm`) binding writing register `d` from
source `s`, the structured linear instruction is

    Lopn [.reg d] (withWidthTag w "SHR") [.reg s, .imm n]      -- e.g. "SHR:64"

— the **base** shift mnemonic (no `:<n>` count in the string) with the count
riding in the `.imm n` operand. This is *exactly* the form

* the existing `legalizeShiftImmLprog` (`Blake2bGThirEmit`,
  `ChaChaQRThirEmit`) produces from the unary `SHR:<n>:64` before byte
  rendering (`legalizeShiftImmInstr (emitted shrImm) = [MOV d,s; SHR:64 d,#n]`),
  and
* the owned printer / `LoweringExtended.lowerAluJ` byte-renders (`"SHR" =>
  .shr dst s`, the two-source `shr r, imm` shape `isShift` recognises).

So `lsemStep`/`lsemStepN` reads `n` from the `.imm` operand **structurally**
(`evalOperandN s w (.imm n) = BitVec.ofNat w n`, then `applyOpnN w "SHR"
[va, BitVec.ofNat w n] = va >>> (BitVec.ofNat w n).toNat = va >>> n`), with **no
string parse of `n`** — the obstruction increment 4 hit is gone.

## Byte output is unchanged

The byte renderer consumes the **structured** form `[d] SHR:64 [d, #n]` on both
paths (the old `string-mnemonic ▸ legalizeShiftImmLprog ▸ render` and this
`structured-mnemonic ▸ render`): `legalizeShiftImmLprog` is the identity on a
bare `SHR:64` (its `parseShiftImm` matches only `SHR:<n>`, not `SHR:64`), and the
printer / ALU table `isShift` recognises `SHR:64` two-source verbatim. So the
shift bytes are *the same instruction the renderer always rendered*; this module
only changes which intermediate the model reads `n` from (operand vs. string),
not the bytes. The SAR path is the byte-equivalent structured twin of the
`SAR:<n>:64` shape `LoweringCoverageCmovSar.lowerSarJ` already renders as
`[mov dst src, sar dst #n]` (an `.imm n` count operand).

## Trocq (`Related`) where it helps

The shift wire-format change is a **representation change**: the abstract shift
value (e.g. `a >>> shiftMask w n`, the dialect denotation) is *realized* by the
structured linear step `structShr w n a := a >>> shiftMask w (BitVec.ofNat w n).toNat`.
This is a `Trocq.Related`-style commuting square
`Related id (a >>> shiftMask w n) (structShr w n a)`
over the identity encoding on `BitVec w` — registered here as the engine
witnesses `relatedStructShr`/`Shl`/`Sar`, the increment's analogue of
`CompilerRegistry`'s `relatedX86Shr` and of `ParamDialectTransport`'s op-leaf
realizers. The per-binding denotation equality is then discharged through
`Trocq.transferRel` (`.rel`). Where Trocq does **not** fit: the *partiality*
descent of `lsemStepN` (an `Option` match on the `LinstrR` syntax, not an op-tree
over a single carrier) and the de-Bruijn `StoreAgreesN` bookkeeping — those reuse
increment 5's machinery directly, as noted at each use.

## Main results

* `comToLprog_faithful_shift`, `owned_lsem_correct_shift` — running
  `straightOpsShift` on the encoded valuation and decoding the result register
  equals `Com.denote`, for `ScalarShiftN`.
* `owned_lsem_correct_shift_of_scalarArithN` — the `ScalarArithN` fragment as a
  special case.
* `lsemLeakSh_straightOps_state_independent` — the leakage of `straightOpsShift`
  is the same from any two states agreeing with a valuation. `lsemLeakSh` reads
  no register value, so this holds for every program of the fragment and is not
  constant-time evidence; constant time of the shipped bytes is
  `DecodedCT.bytesCTCheck_sound`.

The `lsem→bytes` encoder and Sail tables are the declared trusted base.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsem
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemSimulation
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemRobust
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemWidthN
open Transfer (Related transferRel)

/-! ## 1. The structured shift realizers and their `Trocq.Related` squares

A structured shift instruction reads its count from the `.imm` operand, so the
linear step computes `a >>> shiftMask w (BitVec.ofNat w n).toNat`. For an in-range
count `n < 2^w` (every emitted shift count is `< w ≤ 64`) the modular reduction is
vacuous, so this equals the dialect denotation `a >>> shiftMask w n`. Each realizer
is registered as a `Trocq.Related` representation-change witness. -/

/-- The structured **logical right shift** realizer: the value the structured
    linear step `applyOpnN w "SHR" [a, BitVec.ofNat w n]` computes. -/
def structShr (w n : Nat) (a : BitVec w) : BitVec w :=
  a >>> shiftMask w (BitVec.ofNat w n).toNat

/-- The structured **left shift** realizer. -/
def structShl (w n : Nat) (a : BitVec w) : BitVec w :=
  a <<< shiftMask w (BitVec.ofNat w n).toNat

/-- The structured **arithmetic right shift** realizer (`SAR`, sign-extending), by the
    masked count. -/
def structSar (w n : Nat) (a : BitVec w) : BitVec w :=
  BitVec.sshiftRight a (shiftMask w (BitVec.ofNat w n).toNat)

/-- For an in-range count `n < 2^w`, the `BitVec.ofNat` count round-trips: its
    `toNat` is `n`. The single arithmetic fact behind every structured-shift
    realisation (replaces the increment-4 string round-trip `(toString n).toNat?`
    with an operand `toNat`). -/
theorem ofNat_toNat_of_lt {w n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **Representation square (SHR).** For a count `n < 2^w`, the structured shift
    realizer is the logical right shift by the masked count `shiftMask w n`, the
    dialect's denotation of `shrImm w n`. -/
theorem structShr_eq {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    structShr w n a = a >>> shiftMask w n := by
  unfold structShr; rw [ofNat_toNat_of_lt h]

/-- **Representation square (SHL).** For a count `n < 2^w`, the structured shift
    realizer is the left shift by the masked count `shiftMask w n`. -/
theorem structShl_eq {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    structShl w n a = a <<< shiftMask w n := by
  unfold structShl; rw [ofNat_toNat_of_lt h]

/-- **Representation square (SAR).** For a count `n < 2^w`, the structured shift
    realizer at the emitted count `sarCount w n` is the arithmetic right shift by `n`,
    the dialect's denotation of `sarImm w n`. -/
theorem structSar_eq {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    structSar w (sarCount w n) a = BitVec.sshiftRight a n := by
  unfold structSar
  rw [ofNat_toNat_of_lt (lt_of_le_of_lt (Nat.min_le_left n (w - 1)) h : sarCount w n < 2 ^ w),
    sshiftRight_shiftMask_sarCount]

/-- The structured SHR realizer registered as a `Trocq.Related` representation
    change (identity encoding on `BitVec w`): the emitted structured value
    `structShr w n a` realizes the abstract shift `a >>> shiftMask w n`. The
    analogue of `CompilerRegistry.relatedX86Shr`; its `.rel` is `structShr_eq`. -/
def relatedStructShr {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    Related (id : BitVec w → BitVec w) (a >>> shiftMask w n) (structShr w n a) where
  rel := by simpa using (structShr_eq h a).symm

/-- The structured SHL realizer as a `Trocq.Related` square. -/
def relatedStructShl {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    Related (id : BitVec w → BitVec w) (a <<< shiftMask w n) (structShl w n a) where
  rel := by simpa using (structShl_eq h a).symm

/-- The structured SAR realizer as a `Trocq.Related` square. -/
def relatedStructSar {w n : Nat} (h : n < 2 ^ w) (a : BitVec w) :
    Related (id : BitVec w → BitVec w) (BitVec.sshiftRight a n)
      (structSar w (sarCount w n) a) where
  rel := by simpa using (structSar_eq h a).symm

/-! ## 2. The structured shift mnemonics and the `applyOpnN` agreement

The structured shift instruction carries the *base* mnemonic (`withWidthTag w
"SHR"`, etc.), the source register, and the count `.imm`. `lsemStepN`'s generic
binop arm dispatches `applyOpnN` on the stripped base mnemonic; `applyOpnN`
already covers `SHR`/`SHL` (increment 1), so those need no new step arm. `SAR`
is not in `applyOpnN` (it is a sign-aware shift, distinct from the logical
`SHR`), so this fragment carries its own structured-SAR step rather than
widening the shared `applyOpnN`. -/

/-- The `applyOpnN` of the structured `SHR` instruction is `structShr`. -/
theorem applyOpnN_SHR {w n : Nat} (a : BitVec w) :
    applyOpnN w "SHR" [a, BitVec.ofNat w n] = some (structShr w n a) := rfl

/-- The `applyOpnN` of the structured `SHL` instruction is `structShl`. -/
theorem applyOpnN_SHL {w n : Nat} (a : BitVec w) :
    applyOpnN w "SHL" [a, BitVec.ofNat w n] = some (structShl w n a) := rfl

/-- The base shift mnemonics round-trip through `stripWidthTag ∘ withWidthTag`
    (kernel evaluation per width branch, as for `MOV`/`CMOV`/binops). -/
theorem stripWidthTag_withWidthTag_SHR (w : Nat) :
    stripWidthTag (withWidthTag w "SHR") = "SHR" := by
  exact stripWidthTag_withWidthTag w (by decide)

theorem stripWidthTag_withWidthTag_SHL (w : Nat) :
    stripWidthTag (withWidthTag w "SHL") = "SHL" := by
  exact stripWidthTag_withWidthTag w (by decide)

theorem stripWidthTag_withWidthTag_SAR (w : Nat) :
    stripWidthTag (withWidthTag w "SAR") = "SAR" := by
  exact stripWidthTag_withWidthTag w (by decide)

/-! ## 3. Structured shift emission `straightOpsShift`

`straightOpsShift` is the increment-5 `straightOps` extended with structured
shift bindings: a `shrImm w n` binding emits the structured `Lopn [.reg dst]
(withWidthTag w "SHR") [src, .imm n]` (count in the operand), and likewise for
`shlImm`/`sarImm`. The `regArith` and `select` arms emit exactly increment-5's
`opToLinstrR` instruction. This is the linear instruction list the byte renderer
consumes for the shift fragment (the post-`legalizeShiftImmLprog` form). -/

/-- The single structured shift linear instruction for a unary shift binding
    writing `dst` from source operand `src`, base mnemonic `mnem` (`"SHR"` /
    `"SHL"` / `"SAR"`), width `w`, requested count `n`. The logical shifts carry `n`;
    the arithmetic right shift carries the clamped count `sarCount w n < w`. -/
def shiftLinstr (mnem : String) (w : Nat) (dst : String) (src : LOperand) (n : Nat) :
    LinstrR :=
  .Lopn [.reg dst] (withWidthTag w mnem) [src, .imm (if mnem = "SAR" then sarCount w n else n)]

/-- The straight-line `LinstrR` chain a `Com` emits in the shift fragment: like
    increment 5's `straightOps`, but each `shrImm`/`shlImm`/`sarImm` binding
    emits the **structured** shift instruction (count in the `.imm` operand) the
    byte renderer consumes. `regArith`/`select` reuse `opToLinstrR`. -/
def straightOpsShift (nArgs : Nat) :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (curDepth : Nat) → List LinstrR
  | _, _, .ret _, _ => []
  | _, _, .var e body, curDepth =>
      let src := exprArgs curDepth nArgs argName (fun _ => none) e
      let instr : LinstrR :=
        match e.op, src with
        | .shrImm w n, [s] => shiftLinstr "SHR" w (regName curDepth) s n
        | .shlImm w n, [s] => shiftLinstr "SHL" w (regName curDepth) s n
        | .sarImm w n, [s] => shiftLinstr "SAR" w (regName curDepth) s n
        | _, _ => opToLinstrR e.op (regName curDepth) src
      instr :: straightOpsShift nArgs body (curDepth + 1)

/-! ## 4. The shift-fragment source predicate `ScalarShiftN`

Every binding is a `regArith`, a `select`, or an immediate shift `shrImm`/
`shlImm`/`sarImm` whose count is **in range** (`n < 2^w`, true of every emitted
shift count, all `< w ≤ 64`). This subsumes increment 5's `ScalarArithN`. -/

/-- The straight-line **shift-fragment** scalar source: every binding is a
    `regArith`, a width-mixing `select`, or an in-range immediate shift. The
    count-range side condition `n < 2^w` is carried on each shift arm (it holds
    for every emitted shift, whose count is `< w`). -/
inductive ScalarShiftN :
    {Γ : Ctxt jasminDialect} → {t : JasminTy} → Com jasminDialect Γ t → Prop where
  | ret {Γ : Ctxt jasminDialect} {w : Nat} (v : Ctxt.Var Γ (.reg w)) :
      ScalarShiftN (.ret v)
  | var {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat} (bop : JasminBinOp)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarShiftN body) :
      ScalarShiftN (.var ⟨JasminOp.regArith bop w, heq, args⟩ body)
  | sel {Γ : Ctxt jasminDialect} {s : JasminTy} {w : Nat}
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarShiftN body) :
      ScalarShiftN (.var ⟨JasminOp.select w, heq, args⟩ body)
  | shr {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarShiftN body) :
      ScalarShiftN (.var ⟨JasminOp.shrImm w n, heq, args⟩ body)
  | shl {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarShiftN body) :
      ScalarShiftN (.var ⟨JasminOp.shlImm w n, heq, args⟩ body)
  | sar {Γ : Ctxt jasminDialect} {s : JasminTy} {w n : Nat} (hn : n < 2 ^ w)
      (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
      (args : HVector (fun ty => Ctxt.Var Γ ty)
        (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
      {body : Com jasminDialect (.reg w :: Γ) s}
      (hbody : ScalarShiftN body) :
      ScalarShiftN (.var ⟨JasminOp.sarImm w n, heq, args⟩ body)

/-- `ScalarShiftN` subsumes `ScalarArithN`: every increment-5 width-mixed program
    is in the shift fragment. So the increment-5 results are special cases. -/
theorem ScalarShiftN.of_scalarArithN {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (h : ScalarArithN com) : ScalarShiftN com := by
  induction h with
  | ret v => exact .ret v
  | var bop heq args _ ih => exact .var bop heq args ih
  | sel heq args _ ih => exact .sel heq args ih

/-- A `ScalarShiftN` program returns a register. -/
theorem ScalarShiftN.ret_reg {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) : ∃ w, t = .reg w := by
  induction hcom with
  | ret v => exact ⟨_, rfl⟩
  | var _ _ _ _ ih => exact ih
  | sel _ _ _ ih => exact ih
  | shr _ _ _ _ ih => exact ih
  | shl _ _ _ _ ih => exact ih
  | sar _ _ _ _ ih => exact ih

/-! ## 5. The shift-aware step `lsemStepSh`

`SHR`/`SHL` are already in the shared `applyOpnN`, so the structured `SHR`/`SHL`
instruction is faithfully stepped by increment 5's `lsemStepN` (its generic
binop arm reads the `.imm` count operand and runs `applyOpnN`). `SAR` is *not* in
`applyOpnN` (it is the sign-aware shift, distinct from the logical `SHR`), so the
shift-aware step `lsemStepSh` adds exactly one arm — the structured `SAR`
instruction — and delegates **everything else** (control flow, `regArith`,
`select`, `regConst`, and the `SHR`/`SHL` structured forms) verbatim to
`lsemStepN`. Faithful to `eval_instr`'s `Lopn` running the `SAR` `exec_sopn`
(`BitVec.sshiftRight`), reading the count from the `.imm` operand. -/

/-- Recognise a structured `SAR` instruction `Lopn [.reg dst] (…"SAR"…)
    [.reg s, .imm n]` and return `(dst, s, n)`; `none` for anything else. -/
def sarStruct? : LinstrR → Option (String × String × Nat)
  | .Lopn [.reg dst] opn [.reg s, .imm n] =>
      if stripWidthTag opn = "SAR" then some (dst, s, n) else none
  | _ => none

/-- The shift-aware single-step semantics: a structured `SAR` writes
    `BitVec.sshiftRight (read s) (shiftMask w n)` reading `n` from the operand and
    masking it at the source width `w`, as the hardware does; every other
    instruction (including the structured `SHR`/`SHL`, handled by `applyOpnN`)
    delegates to increment 5's `lsemStepN`. Faithful to `eval_instr`'s `Lopn`. -/
def lsemStepSh (i : LinstrR) (s : LstateN) : Option LstateN :=
  match sarStruct? i with
  | some (dst, src, n) =>
      match readReg s (.reg src) with
      | some ⟨w, va⟩ => some ((s.setReg dst (BitVec.sshiftRight va (shiftMask w n))).nextPc)
      | none => none
  | none => lsemStepN i s

/-- On any instruction that is *not* a structured `SAR`, `lsemStepSh` is exactly
    `lsemStepN`. (So increment 5's `regArith`/`select`/`SHR`/`SHL` steps transfer
    unchanged.) -/
theorem lsemStepSh_of_not_sar (i : LinstrR) (s : LstateN) (h : sarStruct? i = none) :
    lsemStepSh i s = lsemStepN i s := by
  simp only [lsemStepSh, h]

/-! ### `lsemStraightSh` / leakage / composition over the shift-aware step -/

/-- Shift-aware straight-line execution: the sequential fold of `lsemStepSh`. -/
def lsemStraightSh : List LinstrR → LstateN → Option LstateN
  | [], s => some s
  | i :: is, s =>
      match lsemStepSh i s with
      | some s' => lsemStraightSh is s'
      | none => none

@[simp] theorem lsemStraightSh_nil (s : LstateN) : lsemStraightSh [] s = some s := rfl

@[simp] theorem lsemStraightSh_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemStraightSh (i :: is) s =
      (match lsemStepSh i s with
        | some s' => lsemStraightSh is s'
        | none => none) := rfl

/-- Shift-aware leakage trace: `linstrLeak` (increment 3) is reused verbatim — it
    reads only the `LinstrR` syntax (the structured shift's source register
    *name* and the public count `.imm`, never a register value). -/
def lsemLeakSh : List LinstrR → LstateN → List JasminLsemRobust.LLeak
  | [], _ => []
  | i :: is, s =>
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepSh i s with
          | some s' => lsemLeakSh is s'
          | none => [])

@[simp] theorem lsemLeakSh_nil (s : LstateN) : lsemLeakSh [] s = [] := rfl

@[simp] theorem lsemLeakSh_cons (i : LinstrR) (is : List LinstrR) (s : LstateN) :
    lsemLeakSh (i :: is) s =
      JasminLsemRobust.linstrLeak i ++
        (match lsemStepSh i s with
          | some s' => lsemLeakSh is s'
          | none => []) := rfl

/-! ## 6. Per-binding agreement for the structured shift instructions

Each shift binding `lsemStepSh`s, from a store agreeing with `V`, to the state
that writes the binding's `Com`-denotation to `regName curDepth`. The denotation
equality is the `Trocq.Related` square (`structShr_eq`/`structShl_eq`/
`structSar_eq`, the in-range count round-trip), applied via `.rel`/`transferRel`. -/

/-- `sarStruct?` is `none` on a structured `SHR` instruction (so `lsemStepSh`
    delegates it to `lsemStepN`). -/
theorem sarStruct?_shiftLinstr_SHR {w : Nat} (dst : String) (src : LOperand) (n : Nat) :
    sarStruct? (shiftLinstr "SHR" w dst src n) = none := by
  simp only [shiftLinstr, sarStruct?]
  cases src <;> simp only []
  · rw [ite_eq_right]; rw [stripWidthTag_withWidthTag_SHR]; decide

/-- `sarStruct?` is `none` on a structured `SHL` instruction. -/
theorem sarStruct?_shiftLinstr_SHL {w : Nat} (dst : String) (src : LOperand) (n : Nat) :
    sarStruct? (shiftLinstr "SHL" w dst src n) = none := by
  simp only [shiftLinstr, sarStruct?]
  cases src <;> simp only []
  · rw [ite_eq_right]; rw [stripWidthTag_withWidthTag_SHL]; decide

/-- `sarStruct?` recognises a structured `SAR` instruction with a `.reg` source, whose
    count is the clamped `sarCount w n`. -/
theorem sarStruct?_shiftLinstr_SAR {w : Nat} (dst src : String) (n : Nat) :
    sarStruct? (shiftLinstr "SAR" w dst (.reg src) n) = some (dst, src, sarCount w n) := by
  simp only [shiftLinstr, sarStruct?, stripWidthTag_withWidthTag_SAR, ite_eq_left]

/-- **Structured `SHR` per-binding step.** From a store agreeing with `V`, the
    structured `SHR` instruction `lsemStepSh`s to the state writing the binding's
    `Com`-denotation `(shrImm w n).denote V` to `regName curDepth`. The count is
    read from the `.imm` operand (no string parse); the denotation equality is
    the `Trocq.Related` square `structShr_eq` via `transferRel`. -/
theorem lsemStepSh_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (shiftLinstr "SHR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons s .nil =>
    have hargs : List.headD (exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.shrImm w n, heq, .cons s .nil⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")
        = resolveVar curDepth nArgs argName (fun _ => none) s := rfl
    rw [hargs, lsemStepSh_of_not_sar _ _ (sarStruct?_shiftLinstr_SHR _ _ _)]
    simp only [shiftLinstr, lsemStepN, readReg_resolveVar s hagree, evalOperandN,
      stripWidthTag_withWidthTag_SHR, applyOpnN]
    -- the structured value `structShr w n (s.lookup V)` equals the denotation
    -- `(shrImm w n).denote V = s.lookup V >>> shiftMask w n` by the `Related` square.
    show some ((st.setReg (regName curDepth) (structShr w n (s.lookup V))).nextPc) = _
    -- `structShr w n a = a >>> shiftMask w n = (shrImm w n).denote` via the square
    -- `structShr_eq` (equivalently `(transferRel (relatedStructShr hn a)).symm`).
    rw [structShr_eq hn (s.lookup V)]; rfl

/-- **Structured `SHL` per-binding step** (parallel to `lsemStepSh_shr`). -/
theorem lsemStepSh_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (shiftLinstr "SHL" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons s .nil =>
    have hargs : List.headD (exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.shlImm w n, heq, .cons s .nil⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")
        = resolveVar curDepth nArgs argName (fun _ => none) s := rfl
    rw [hargs, lsemStepSh_of_not_sar _ _ (sarStruct?_shiftLinstr_SHL _ _ _)]
    simp only [shiftLinstr, lsemStepN, readReg_resolveVar s hagree, evalOperandN,
      stripWidthTag_withWidthTag_SHL, applyOpnN]
    show some ((st.setReg (regName curDepth) (structShl w n (s.lookup V))).nextPc) = _
    rw [structShl_eq hn (s.lookup V)]; rfl

/-- **Structured `SAR` per-binding step.** From a store agreeing with `V`, the
    structured `SAR` instruction `lsemStepSh`s to the state writing the binding's
    `Com`-denotation `(sarImm w n).denote V = BitVec.sshiftRight (s.lookup V) n`
    to `regName curDepth`, reading the count from the `.imm` operand. This uses
    the dedicated `SAR` arm of `lsemStepSh` (`SAR` is not in `applyOpnN`); the
    denotation equality is the `Trocq.Related` square `structSar_eq`. -/
theorem lsemStepSh_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w n : Nat} (_hn : n < 2 ^ w)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (shiftLinstr "SAR" w (regName curDepth)
          (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
            (.reg "")) n) st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  match args with
  | .cons s .nil =>
    have hres : resolveVar curDepth nArgs argName (fun _ => none) s
        = .reg (operandName (resolveVar curDepth nArgs argName (fun _ => none) s)) :=
      resolveVar_isReg s
    have hargs : List.headD (exprArgs curDepth nArgs argName (fun _ => none)
        (⟨JasminOp.sarImm w n, heq, .cons s .nil⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")
        = resolveVar curDepth nArgs argName (fun _ => none) s := rfl
    -- read the source value out of the store at width `w` (via the agreement)
    have hs := hagree s
    rw [evalOperandN_resolveVar] at hs
    rw [hargs]
    -- the `SAR` instruction has a `.reg` source, so `lsemStepSh` takes its SAR
    -- arm, which reads the clamped count `sarCount w n` as the `.imm` operand's
    -- literal (a `Nat`) and masks it at width `w`; `sshiftRight_shiftMask_sarCount`
    -- turns the step value into `BitVec.sshiftRight (s.lookup V) n`, which is
    -- definitionally `(sarImm w n).denote V`.
    rw [hres, lsemStepSh, sarStruct?_shiftLinstr_SAR]
    simp only [readReg_of_getW hs]
    rw [sshiftRight_shiftMask_sarCount]
    rfl

/-! ## 7. `straightOpsShift` unfolding on each binding head

Each `straightOpsShift` cons exposes the instruction the per-binding step lemmas
consume. The `regArith`/`select` arms reduce to the increment-5 `opToLinstrR`
instruction; the shift arms to `shiftLinstr`. -/

/-- `straightOpsShift` on a `shrImm` binding: the head is the structured `SHR`
    instruction, the tail is the recursive chain. -/
theorem straightOpsShift_shr {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shrImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shrImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsShift nArgs (.var ⟨JasminOp.shrImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SHR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shrImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsShift nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

/-- `straightOpsShift` on a `shlImm` binding. -/
theorem straightOpsShift_shl {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.shlImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.shlImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsShift nArgs (.var ⟨JasminOp.shlImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SHL" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.shlImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsShift nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

/-- `straightOpsShift` on a `sarImm` binding. -/
theorem straightOpsShift_sar {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w n : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.sarImm w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.sarImm w n)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsShift nArgs (.var ⟨JasminOp.sarImm w n, heq, args⟩ body) curDepth =
      shiftLinstr "SAR" w (regName curDepth)
        (List.headD (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.sarImm w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))) (.reg "")) n
      :: straightOpsShift nArgs body (curDepth + 1) := by
  match args with
  | .cons _ .nil => rfl

/-- `straightOpsShift` on a `regArith` binding: the increment-5 `opToLinstrR`
    instruction (the shift match falls through to the default arm). -/
theorem straightOpsShift_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsShift nArgs (.var ⟨JasminOp.regArith bop w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsShift nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ .nil) => rfl

/-- `straightOpsShift` on a `select` binding: the increment-5 `opToLinstrR`
    `CMOV` instruction. -/
theorem straightOpsShift_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {s : JasminTy} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (body : Com jasminDialect (.reg w :: Γ) s) :
    straightOpsShift nArgs (.var ⟨JasminOp.select w, heq, args⟩ body) curDepth =
      opToLinstrR (JasminOp.select w) (regName curDepth)
        (exprArgs curDepth nArgs argName (fun _ => none)
          (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)))
      :: straightOpsShift nArgs body (curDepth + 1) := by
  match args with
  | .cons _ (.cons _ (.cons _ .nil)) => rfl

/-! ## 8. The `regArith`/`select` instructions step via `lsemStepSh` = `lsemStepN`

`opToLinstrR (regArith …)` / `opToLinstrR (select …)` are not structured `SAR`
(`binOpName` never yields `SAR`; `select` yields `CMOV`), so `lsemStepSh`
delegates them to `lsemStepN` and the increment-5 per-binding steps transfer. -/

/-- `binOpName` never produces the `SAR` mnemonic. -/
theorem binOpName_ne_SAR (bop : JasminBinOp) : binOpName bop ≠ "SAR" := by
  cases bop <;> decide

/-- `sarStruct?` of an `Lopn` whose stripped mnemonic is not `"SAR"` is `none`
    (regardless of operand shape). -/
theorem sarStruct?_of_ne {dst : String} {opn : String} {srcs : List LOperand}
    (h : stripWidthTag opn ≠ "SAR") :
    sarStruct? (.Lopn [.reg dst] opn srcs) = none := by
  rcases srcs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
  · rfl
  · cases a <;> rfl
  · cases a <;> cases b <;> simp only [sarStruct?, ite_eq_right h]
  · cases a <;> simp only [sarStruct?]

/-- The `regArith` `opToLinstrR` image is never a structured `SAR`. -/
theorem sarStruct?_regArith {w : Nat} (bop : JasminBinOp) (dst : String)
    (srcs : List LOperand) :
    sarStruct? (opToLinstrR (JasminOp.regArith bop w) dst srcs) = none := by
  rw [opToLinstrR]
  exact sarStruct?_of_ne (by rw [stripWidthTag_withWidthTag_binOpName]; exact binOpName_ne_SAR bop)

/-- The `select` `opToLinstrR` image is never a structured `SAR` (the `CMOV`
    mnemonic). -/
theorem sarStruct?_select {w : Nat} (dst : String) (srcs : List LOperand) :
    sarStruct? (opToLinstrR (JasminOp.select w) dst srcs) = none := by
  rw [opToLinstrR]
  exact sarStruct?_of_ne (by rw [stripWidthTag_withWidthTag_CMOV]; decide)

/-- The `regArith` binding steps via `lsemStepSh` to its denotation (increment 5's
    `lsemStepN_var`, transferred through `lsemStepSh = lsemStepN`). -/
theorem lsemStepSh_var {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat} (bop : JasminBinOp)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regArith bop w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regArith bop w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (opToLinstrR (JasminOp.regArith bop w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regArith bop w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSh_of_not_sar _ _ (sarStruct?_regArith _ _ _)]
  exact lsemStepN_var bop heq args hagree

/-- The `rorImm` `opToLinstrR` image is never a structured `SAR`. -/
theorem sarStruct?_ror {w k : Nat} (dst : String) (srcs : List LOperand) :
    sarStruct? (opToLinstrR (JasminOp.rorImm w k) dst srcs) = none := by
  rw [opToLinstrR]
  exact sarStruct?_of_ne (by
    rw [JasminLsemWidthN.stripWidthTag_withWidthTag_ROR]
    exact JasminLsemWidthN.ror_core_ne_of_head k (by decide))

/-- The `rorImm` binding steps via `lsemStepSh` to its denotation (`lsemStepN_ror`). -/
theorem lsemStepSh_ror {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w k : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.rorImm w k) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.rorImm w k)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (opToLinstrR (JasminOp.rorImm w k) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.rorImm w k, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.rorImm w k, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote
          V)).nextPc) := by
  rw [lsemStepSh_of_not_sar _ _ (sarStruct?_ror _ _)]
  exact JasminLsemWidthN.lsemStepN_ror heq args hagree

/-- The `select` binding steps via `lsemStepSh` to its denotation (increment 5's
    `lsemStepN_sel`, transferred through `lsemStepSh = lsemStepN`). -/
theorem lsemStepSh_sel {nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} {w : Nat}
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.select w) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.select w)))
    (hagree : StoreAgreesN nArgs curDepth st V) :
    lsemStepSh
        (opToLinstrR (JasminOp.select w) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.select w, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSh_of_not_sar _ _ (sarStruct?_select _ _)]
  exact lsemStepN_sel heq args hagree

/-- The `regConst` `opToLinstrR` image is never a structured `SAR` (the `MOV`
    mnemonic). -/
theorem sarStruct?_regConst {w n : Nat} (dst : String) (srcs : List LOperand) :
    sarStruct? (opToLinstrR (JasminOp.regConst w n) dst srcs) = none := by
  rw [opToLinstrR]
  exact sarStruct?_of_ne (by
    rw [CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemScalar.stripWidthTag_withWidthTag_MOV]
    decide)

/-- The `regConst` binding steps via `lsemStepSh` to its denotation (increment 5's
    `lsemStepN_const`, transferred through `lsemStepSh = lsemStepN`). The `hwn`
    hypothesis pins the constant's width on the two wire-distinguished widths. -/
theorem lsemStepSh_const {w nArgs curDepth : Nat} {Γ : Ctxt jasminDialect}
    {V : Ctxt.Valuation Γ} {st : LstateN} (n : Nat) (hwn : w = 64 ∨ w = 32)
    (heq : DialectSignature.ret (d := jasminDialect) (JasminOp.regConst w n) = .reg w)
    (args : HVector (fun ty => Ctxt.Var Γ ty)
      (DialectSignature.sig (d := jasminDialect) (JasminOp.regConst w n))) :
    lsemStepSh
        (opToLinstrR (JasminOp.regConst w n) (regName curDepth)
          (exprArgs curDepth nArgs argName (fun _ => none)
            (⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w))))
        st =
      some ((st.setReg (regName curDepth)
        ((⟨JasminOp.regConst w n, heq, args⟩ : Expr jasminDialect Γ (.reg w)).denote V)).nextPc) := by
  rw [lsemStepSh_of_not_sar _ _ (sarStruct?_regConst _ _)]
  exact lsemStepN_const (V := V) n hwn heq args

/-! ## 9. The core shift-fragment straight-line simulation

Same induction skeleton as increment 5's `lsemStraightN_straightOps`, with the
three new shift arms closed by `lsemStepSh_shr`/`shl`/`sar` + `StoreAgreesN.step`,
and the `regArith`/`select` arms by `lsemStepSh_var`/`lsemStepSh_sel`. -/

/-- **Core simulation (parametrized by an agreeing start state), shift fragment.**
    From any width-tagged store `st` agreeing with `V` at depth `curDepth`,
    running the shift-fragment `.var`-chain `straightOpsShift` succeeds, lands in a
    store agreeing with the binding-extended valuation, and reads `Com.denote com
    V` (transported to its return width) at the return register. -/
theorem lsemStraightShift_straightOps {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) :
    ∀ {nArgs curDepth : Nat} {st : LstateN} {V : Ctxt.Valuation Γ}
      {w : Nat} (hw : t = .reg w),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth st V →
      ∃ st', lsemStraightSh (straightOpsShift nArgs com curDepth) st = some st' ∧
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
      have hstep := lsemStepSh_var (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        bop heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.regArith bop _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsShift_var, lsemStraightSh_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sel heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSh_sel (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.select _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsShift_sel, lsemStraightSh_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shr hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSh_shr (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shrImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsShift_shr, lsemStraightSh_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | shl hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSh_shl (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.shlImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsShift_shl, lsemStraightSh_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret
  | sar hn heq args hbody ih =>
      intro nArgs curDepth st V w hw hlen harg hagree
      have hstep := lsemStepSh_sar (V := V) (st := st) (nArgs := nArgs) (curDepth := curDepth)
        hn heq args hagree
      have hagree' : StoreAgreesN nArgs (curDepth + 1) _ _ := StoreAgreesN.step
        ((⟨JasminOp.sarImm _ _, heq, args⟩ : Expr jasminDialect _ _).denote V)
        hlen harg hagree
      obtain ⟨st', hrun, hret⟩ := ih hw (by simp [List.length_cons, hlen]) (by omega) hagree'
      refine ⟨st', ?_, ?_⟩
      · rw [straightOpsShift_sar, lsemStraightSh_cons, hstep]; exact hrun
      · simp only [comRetReg]; exact hret

/-! ## 10. Faithfulness and leak state-independence

`encodeN`/`decodeN`/`encodeN_StoreAgreesN` are reused verbatim from increment 5
(the start-state encoding is op-agnostic). The leak induction reuses the same
per-binding success facts. -/

/-- **Straight-line linearizer simulation, shift fragment.** Running the
    shift-fragment `.var`-chain `straightOpsShift` from the encoded argument
    valuation and decoding the result register at width `w` equals the source
    program's `Com.denote`. -/
theorem comToLprog_lsemShift {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    ∃ st', lsemStraightSh (straightOpsShift Γ.length com Γ.length) (encodeN V) = some st' ∧
      decodeN st' (comRetReg Γ.length argName com Γ.length) w =
        some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hret⟩ :=
    lsemStraightShift_straightOps hcom hw (nArgs := Γ.length) (curDepth := Γ.length)
      (st := encodeN V) (V := V) rfl le_rfl (encodeN_StoreAgreesN V)
  exact ⟨st', hrun, by simpa only [decodeN, evalOperandN] using hret⟩

/-- **Faithfulness (packaged), shift fragment.** -/
theorem comToLprog_faithful_shift {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightSh (straightOpsShift Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) := by
  obtain ⟨st', hrun, hdec⟩ := comToLprog_lsemShift hcom hw V
  rw [hrun, Option.bind_some, hdec]

/-- **Leak state-independence, shift fragment.** The leakage trace of the
    shift-fragment `.var`-chain is the same from any two initial states agreeing
    with the same valuation: every head (`regArith`, `select`, or an immediate
    shift) has a `linstrLeak` reading only syntax — for a shift, the source
    register name and the count `.imm`, never a value — and `lsemStepSh`s
    successfully, so both states run the same tail. Since `linstrLeak` reads no
    value, the statement holds for every program of the fragment and is not
    constant-time evidence. -/
theorem lsemLeakSh_straightOps_state_independent {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) :
    ∀ {nArgs curDepth : Nat} {V₁ V₂ : Ctxt.Valuation Γ} (s₁ s₂ : LstateN),
      Γ.length = curDepth → nArgs ≤ curDepth →
      StoreAgreesN nArgs curDepth s₁ V₁ → StoreAgreesN nArgs curDepth s₂ V₂ →
      lsemLeakSh (straightOpsShift nArgs com curDepth) s₁ =
        lsemLeakSh (straightOpsShift nArgs com curDepth) s₂ := by
  induction hcom with
  | ret v => intro nArgs curDepth V₁ V₂ s₁ s₂ _ _ _ _; rfl
  | var bop heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSh_var (V := V₁) bop heq args hag1
      have hstep2 := lsemStepSh_var (V := V₂) bop heq args hag2
      rw [straightOpsShift_var]
      simp only [lsemLeakSh_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sel heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSh_sel (V := V₁) heq args hag1
      have hstep2 := lsemStepSh_sel (V := V₂) heq args hag2
      rw [straightOpsShift_sel]
      simp only [lsemLeakSh_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shr hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSh_shr (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSh_shr (V := V₂) hn heq args hag2
      rw [straightOpsShift_shr]
      simp only [lsemLeakSh_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | shl hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSh_shl (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSh_shl (V := V₂) hn heq args hag2
      rw [straightOpsShift_shl]
      simp only [lsemLeakSh_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)
  | sar hn heq args hbody ih =>
      intro nArgs curDepth V₁ V₂ s₁ s₂ hlen harg hag1 hag2
      have hstep1 := lsemStepSh_sar (V := V₁) hn heq args hag1
      have hstep2 := lsemStepSh_sar (V := V₂) hn heq args hag2
      rw [straightOpsShift_sar]
      simp only [lsemLeakSh_cons, hstep1, hstep2]
      refine congrArg (JasminLsemRobust.linstrLeak _ ++ ·) ?_
      exact ih _ _ (by simp [List.length_cons, hlen]) (by omega)
        (StoreAgreesN.step _ hlen harg hag1) (StoreAgreesN.step _ hlen harg hag2)

/-! ## 11. Functional correctness of `straightOpsShift` -/

/-- **Functional correctness for the shift fragment (`regArith ∪ select ∪ shrImm
    ∪ shlImm ∪ sarImm`).** For a shift-fragment scalar straight-line `Com` with
    return type `.reg w`, running the structured `.var`-chain `straightOpsShift`
    on the encoded argument valuation and decoding the result register at width
    `w` yields exactly `com.denote V`. The shift counts are read from the `.imm`
    operand of the structured form `[d] SHR:64 [d, #n]` the byte renderer
    consumes. This is `comToLprog_faithful_shift`, stated at this module's entry
    point. -/
theorem owned_lsem_correct_shift {Γ : Ctxt jasminDialect} {t : JasminTy}
    {com : Com jasminDialect Γ t} (hcom : ScalarShiftN com) {w : Nat} (hw : t = .reg w)
    (V : Ctxt.Valuation Γ) :
    (lsemStraightSh (straightOpsShift Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) :=
  comToLprog_faithful_shift hcom hw V

/-- The `ScalarArithN` fragment is a special case of the shift fragment: the
    conclusion is `owned_lsem_correct_shift` at `ScalarShiftN.of_scalarArithN`. -/
theorem owned_lsem_correct_shift_of_scalarArithN {Γ : Ctxt jasminDialect}
    {t : JasminTy} {com : Com jasminDialect Γ t} (hcom : ScalarArithN com)
    {w : Nat} (hw : t = .reg w) (V : Ctxt.Valuation Γ) :
    (lsemStraightSh (straightOpsShift Γ.length com Γ.length) (encodeN V)).bind
        (fun st' => decodeN st' (comRetReg Γ.length argName com Γ.length) w) =
      some (hw ▸ com.denote V : ⟦(JasminTy.reg w)⟧) :=
  owned_lsem_correct_shift (ScalarShiftN.of_scalarArithN hcom) hw V

end CatCrypt.Crypto.SecureCompilation.VIR.JasminLsemShift
