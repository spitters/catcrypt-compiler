/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence

/-!
# Frontend coincidence (immediate-shift extension): the two frontend denotations
# COINCIDE on the immediate logical-shift arms

This module **extends** the base-case coincidence result of
`CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence` (which covered
variable/literal atoms and the binary ALU heads `add/sub/mul/and/xor`) to the
**immediate logical shifts** `shr`/`shl`. It reuses, verbatim, the base file's
`EnvAgree`, `atomSExpr`, and `atom_coincides`, and adds the shift mapping plus
the shift apply-lemmas and the shift-arm coincidence theorems.

## What an immediate shift looks like on each path

* **Path A — scalar-THIR-direct.** `ImpExpr.denoteScalar` dispatches a
  `.app f [a, .lit l]` whose head `f` is a recognised shift (`recogShift f =
  some k`) to `ShiftKind.apply k av n`, where `av` is the atom denotation of `a`
  and `n = litNat? l` is a **compile-time immediate** `Nat` count
  (`ImpExprToThir`, `denoteScalar`'s `recogShift` arm). For the logical shifts:
  `ShiftKind.apply .shr av n = av >>> n` and `ShiftKind.apply .shl av n =
  av <<< n`.

* **Path B — whole-function LowCT.** The `SExpr` shift nodes `SShr`/`SShl` take a
  *dynamic* `SExpr` shift operand evaluated through `(b.evalBV β).toNat`
  (`Jasmin.LowCT`):
  `SExpr.evalBV β (.SShr a b) = (a.evalBV β) >>> (b.evalBV β).toNat`, and
  symmetrically for `.SShl`. The Path-B image of an *immediate* shift therefore
  pins the dynamic operand to the literal node `.SLit n`, whose `evalBV` is
  `BitVec.ofNat 64 n` and whose `.toNat` is `n` exactly when `n < 2 ^ 64`.

## The mapping (local; we do not edit the base `toSExpr`)

`shiftSExpr` sends an immediate-shift `ImpExpr` to its `SExpr` image: the atom
`a` is mapped by the base file's `atomSExpr`, and the *count* `n` becomes the
literal node `.SLit n`:

```
shr a n  ↦  SShr (atomSExpr a) (SLit n)
shl a n  ↦  SShl (atomSExpr a) (SLit n)
```

This deliberately lives in this file rather than in the base `toSExpr` (which
returns `none` on every shift/rotate) so the base-case file's clean
`toSExpr`-keyed statement is preserved.

## The honest side condition: `n < 2 ^ 64`

Path A uses the count `n : Nat` *directly* as the BitVec shift amount; Path B
uses `(SExpr.evalBV β (.SLit n)).toNat = (BitVec.ofNat 64 n).toNat = n % 2 ^ 64`.
These agree iff `n % 2 ^ 64 = n`, i.e. **`n < 2 ^ 64`** (lemma
`ofNat_toNat_of_lt`). This is the cleanest *true* hypothesis:

* It is **not** `n < 64`. For `64 ≤ n < 2 ^ 64` both paths still agree: each uses
  the *same* amount `n`, and a `BitVec 64` shifted by `≥ 64` is all-zeros on both
  — so the coincidence holds for all `n < 2 ^ 64`, not just sub-width counts.
* It **fails** only for `n ≥ 2 ^ 64`, where Path B's amount degrades to
  `n % 2 ^ 64` (which may be `< 64`, giving a *non-zero* result) while Path A
  still uses the full `n` (giving `0`). We do not paper over this: the side
  condition is stated as a hypothesis on the theorems. In practice an
  extraction's immediate shift count is a small `u32`/`u8`, well under `2 ^ 64`.

## Honesty note (what is NOT claimed — consistent with the base file)

* **Arithmetic shift `sar` is out.** `SExpr.evalBV (.SShr …)` is the *logical*
  right shift `>>>`; the LowCT side comments `SShr` as "right shift (truncating,
  LOGICAL)". Path A's `ShiftKind.apply .sar = BitVec.sshiftRight` is the
  *arithmetic* shift. There is no logical/arithmetic node confusion here: we map
  only the logical shifts `shr`/`shl`, and do **not** claim `sar` coincides with
  any `SExpr` node.
* **Rotate `ror` is out.** `SExpr` has **no rotate node at all**, so
  `ShiftKind.apply .ror av n = av.rotateRight n` has no `SExpr` image. Stated,
  not forced.
* **`or`/`andn` remain out** on the binary side (no `SOr`/`SAndn` node), exactly
  as in the base file.

Each lemma below is about **both** `denoteScalar`/`ShiftKind.apply`
(Path A) **and** `SExpr.evalBV` (Path B); none is a restatement of one side.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence

open _root_.Hax
open CatCrypt.Crypto.SecureCompilation.ImpExprToThir
open CatCrypt.Crypto.Jasmin.LowCT
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (JasminBinOp)

/-! ## §1  The `SExpr` image of an immediate logical shift

The covered logical-shift kinds and their `SExpr` constructors: `shr ↦ SShr`,
`shl ↦ SShl`. The arithmetic shift `sar` and the rotate `ror` have no logical
`SExpr` image (see the module docstring) and so map to `none`. -/

/-- The `SExpr` binary constructor for a recognised *logical* shift kind, mapped
    arm-for-arm onto `SExpr`. `sar`/`ror` : `SExpr`'s `SShr` is the **logical**
    right shift and `SExpr` has **no rotate** node, so the coincident shift
    fragment is exactly `shr`/`shl`. -/
def shiftCtor : ShiftKind → Option (SExpr → SExpr → SExpr)
  | .shr => some .SShr
  | .shl => some .SShl
  | _    => none

/-- `SExpr` image of an *immediate logical shift* `ImpExpr`: a recognised logical
    shift head (`recogShift f = some k`, `shiftCtor k = some mk`) applied to an
    atom argument `a` (image `atomSExpr a`) and a *literal* count `l` (image
    `.SLit n`, `n = litNat? l`). Anything else — `sar`/`ror`, a non-literal shift
    amount, a non-atom shifted value — is `none`. The dynamic `SExpr` shift
    operand is pinned to the literal node `.SLit n`. -/
def shiftSExpr : ImpExpr → Option SExpr
  | .app f [a, .lit l] =>
      (recogShift f).bind fun k =>
        (shiftCtor k).bind fun mk =>
          (atomSExpr a).bind fun sa =>
            (litNat? l).map fun n => mk sa (.SLit n)
  | _ => none

/-! ## §2  The literal-count and shift apply-lemmas

`SExpr.evalBV β (.SLit n) = BitVec.ofNat 64 n`, whose `.toNat` is `n` under the
honest side condition `n < 2 ^ 64`; the `SShr`/`SShl` nodes on a literal operand
then evaluate to `av >>> n` / `av <<< n`, matching `ShiftKind.apply`. -/

/-- The literal-node `evalBV` reading: `evalBV β (.SLit n) = BitVec.ofNat 64 n`.
    About Path B (`SExpr.evalBV`). -/
theorem evalBV_SLit (β : String → BitVec 64) (n : Nat) :
    SExpr.evalBV β (.SLit n) = BitVec.ofNat 64 n := rfl

/-- Under the side condition `n < 2 ^ 64`, the `.SLit n` shift operand's
    `(evalBV β _).toNat` is exactly `n` — the amount Path A uses directly.
    This is the alignment fact for the immediate-shift coincidence;
    it is the *only* place the side condition is consumed. -/
theorem ofNat_toNat_of_lt (β : String → BitVec 64) {n : Nat} (h : n < 2 ^ 64) :
    (SExpr.evalBV β (.SLit n)).toNat = n := by
  rw [evalBV_SLit, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- **`shr` apply-agreement.** Under `n < 2 ^ 64`, Path A's `ShiftKind.apply .shr
    av n = av >>> n` agrees with the Path-B `SShr` node on a literal count:
    `evalBV β (.SShr a (.SLit n)) = (evalBV β a) >>> n`. About both
    `ShiftKind.apply` (LHS, via `av := evalBV β a`) and `SExpr.evalBV` (RHS). -/
theorem apply_shr_eq_evalBV (β : String → BitVec 64) (sa : SExpr) {n : Nat}
    (h : n < 2 ^ 64) :
    ShiftKind.apply .shr (SExpr.evalBV β sa) n
      = SExpr.evalBV β (.SShr sa (.SLit n)) := by
  show (SExpr.evalBV β sa) >>> n = (SExpr.evalBV β sa) >>> (SExpr.evalBV β (.SLit n)).toNat
  rw [ofNat_toNat_of_lt β h]

/-- **`shl` apply-agreement.** Under `n < 2 ^ 64`, Path A's `ShiftKind.apply .shl
    av n = av <<< n` agrees with the Path-B `SShl` node on a literal count:
    `evalBV β (.SShl a (.SLit n)) = (evalBV β a) <<< n`. About both
    `ShiftKind.apply` and `SExpr.evalBV`. -/
theorem apply_shl_eq_evalBV (β : String → BitVec 64) (sa : SExpr) {n : Nat}
    (h : n < 2 ^ 64) :
    ShiftKind.apply .shl (SExpr.evalBV β sa) n
      = SExpr.evalBV β (.SShl sa (.SLit n)) := by
  show (SExpr.evalBV β sa) <<< n = (SExpr.evalBV β sa) <<< (SExpr.evalBV β (.SLit n)).toNat
  rw [ofNat_toNat_of_lt β h]

/-- The shift apply-agreement bundled for `shiftSExpr`'s covered set: if
    `shiftCtor k = some mk`, then `ShiftKind.apply k` on a value/immediate-count
    agrees with the `evalBV` of `mk` applied to that value's image and `.SLit n`,
    under `n < 2 ^ 64`. The generic per-kind fact `shift_coincides` consumes,
    proved by case on the (two covered) logical-shift kinds. -/
theorem apply_eq_evalBV_of_shiftCtor (β : String → BitVec 64)
    {k : ShiftKind} {mk : SExpr → SExpr → SExpr} (hmk : shiftCtor k = some mk)
    (sa : SExpr) {n : Nat} (h : n < 2 ^ 64) :
    ShiftKind.apply k (SExpr.evalBV β sa) n
      = SExpr.evalBV β (mk sa (.SLit n)) := by
  cases k <;> simp only [shiftCtor, Option.some.injEq, reduceCtorEq] at hmk <;>
    subst hmk
  · exact apply_shr_eq_evalBV β sa h
  · exact apply_shl_eq_evalBV β sa h

/-- A recognised shift head is never a recognised binop head: `recogShift f =
    some k` forces `recogBin f = none`. The shift heads (`rotate_right`, `sar`,
    `shr`, `shl`, and their capitalized/aliased twins) are disjoint from the
    binop heads (`BitXor`/`BitAnd`/`BitOr`/`add`/`mul`/`sub` families). Proved by
    unfolding both recognisers and discharging the string disequalities. This is
    the disjointness fact the coincidence theorems need so the `denoteScalar`
    `.app` match falls through to the `recogShift` arm. -/
theorem recogBin_none_of_recogShift {f : String} {k : ShiftKind}
    (hf : recogShift f = some k) : recogBin f = none := by
  unfold recogShift at hf
  unfold recogBin
  -- Resolve `f` against the shift-head string guards; each branch fixes the
  -- binop guards to `false`.
  split_ifs at hf with h1 h2 h3 h4 <;>
    simp_all only [Option.some.injEq] <;>
    (first
      | (rcases h1 with h | h <;> subst h <;> simp)
      | (rcases h2 with h | h | h <;> subst h <;> simp)
      | (rcases h3 with h | h | h <;> subst h <;> simp)
      | (rcases h4 with h | h | h <;> subst h <;> simp))

/-! ## §3  Immediate-shift coincidence (the deliverable)

The inductive STEP for one immediate logical shift, in the style of the base
file's `bin_coincides`: Path A `denoteScalar (.app f [a, .lit l])` dispatches via
`recogShift` to `ShiftKind.apply k` on the atom denotation of `a` and the
immediate count `n = litNat? l`; Path B `evalBV β (mk sa (.SLit n))` is the
matching `SExpr` shift node on the literal count. Under `EnvAgree` (consumed via
`atom_coincides` on `a`) and the honest side condition `n < 2 ^ 64`, the two
coincide. -/

/-- **Immediate logical-shift step coincidence (per shift).** A recognised
    logical-shift head `f` (`recogShift f = some k`) in the covered set
    (`shiftCtor k = some mk`), applied to an atom `a` (image `sa`) and a literal
    count `l` (`litNat? l = some n`, `n < 2 ^ 64`), coincides between the paths:

    * Path A `denoteScalar (.app f [a, .lit l])` routes through the `recogShift`
      arm to `ShiftKind.apply k av n`, and
    * Path B `evalBV β (mk sa (.SLit n))` is the matching `SExpr` shift node,

    and the two are equal (modulo the `some`). Consumes the atom-leaf coincidence
    (`atom_coincides`) on `a` and the per-kind agreement
    (`apply_eq_evalBV_of_shiftCtor`). About both `denoteScalar` (LHS)
    and `SExpr.evalBV` (RHS). The crucial subtlety: `recogBin f` must be `none`
    so `denoteScalar` falls through to its `recogShift` arm (a recognised shift
    head is never a recognised binop head, so `recogBin f = none` is forced; we
    take it as a hypothesis, discharged below from `recogShift f = some k`). -/
theorem shift_coincides {nIn : Nat} (params : List String) (I : Fin nIn → BitVec 64)
    (ρ : String → Option (BitVec 64)) (β : String → BitVec 64)
    (hβ : EnvAgree params I ρ β)
    {f : String} {op? : Option JasminBinOp} (hbin : recogBin f = op?)
    (hbinNone : op? = none)
    {k : ShiftKind} (hf : recogShift f = some k)
    {a : ImpExpr} {l : ImpLit} {sa : SExpr} {n : Nat}
    (ha : atomSExpr a = some sa) (hl : litNat? l = some n) (hn : n < 2 ^ 64)
    {mk : SExpr → SExpr → SExpr} (hmk : shiftCtor k = some mk) :
    ImpExpr.denoteScalar params I (.app f [a, .lit l]) ρ
      = some (SExpr.evalBV β (mk sa (.SLit n))) := by
  subst hbinNone
  -- Path A: unfold `denoteScalar`; the `recogBin f = none` match falls through
  -- to the `recogShift f = some k` arm on `[a, .lit l]`.
  unfold ImpExpr.denoteScalar
  rw [hbin, hf]
  -- Collapse the (now constructor-headed) inner `recogShift`/`args` match.
  simp only []
  -- The shifted value's atom denotation coincides; the count is `n`.
  rw [atom_coincides params I ρ β hβ a ha, hl]
  -- Now `some (evalBV β sa) bind (fun av => some (k.apply av n))`; collapse and
  -- apply the per-kind agreement.
  simp only [Option.bind_some, Option.map_some, Option.some.injEq]
  exact apply_eq_evalBV_of_shiftCtor β hmk sa hn

/-- **Covered immediate-shift coincidence (keyed off `shiftSExpr`).** For any
    immediate logical shift `ImpExpr` that `shiftSExpr` accepts, Path A
    `denoteScalar` equals `some` of Path B `evalBV` under `EnvAgree`, given the
    honest side condition that the recovered immediate count is `< 2 ^ 64`. This
    is the immediate-shift analogue of the base file's
    `denoteScalar_coincides_evalBV`, with `toSExpr` replaced by `shiftSExpr`. -/
theorem denoteScalar_coincides_evalBV_shift {nIn : Nat} (params : List String)
    (I : Fin nIn → BitVec 64) (ρ : String → Option (BitVec 64))
    (β : String → BitVec 64) (hβ : EnvAgree params I ρ β)
    (e : ImpExpr) {s : SExpr} (hs : shiftSExpr e = some s)
    -- the recovered immediate count is in range (consumed via `shift_coincides`);
    -- stated as the honest `n < 2 ^ 64` hypothesis on the literal of `e`.
    (hrange : ∀ f a l, e = .app f [a, .lit l] → ∀ n, litNat? l = some n → n < 2 ^ 64) :
    ImpExpr.denoteScalar params I e ρ = some (SExpr.evalBV β s) := by
  -- `shiftSExpr` only succeeds on `.app f [a, .lit l]`.
  match e, hs with
  | .app f [a, .lit l], hs =>
    simp only [shiftSExpr, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hs
    obtain ⟨k, hf, mk, hmk, sa, ha, n, hl, hs⟩ := hs
    subst hs
    -- A recognised shift head is never a recognised binop head: `recogBin f =
    -- none`. We obtain this from `recogShift f = some k` by `cases` on the
    -- string guards. Rather than re-derive, route through `shift_coincides`
    -- with `recogBin f` left abstract and the `none` fact proved here.
    have hbinNone : recogBin f = none := recogBin_none_of_recogShift hf
    exact shift_coincides params I ρ β hβ hbinNone rfl hf ha hl
      (hrange f a l rfl n hl) hmk

end CatCrypt.Crypto.SecureCompilation.Dialects.FrontendCoincidence
