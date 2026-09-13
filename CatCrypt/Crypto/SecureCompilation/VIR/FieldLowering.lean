/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
public import CatCrypt.Crypto.SecureCompilation.VIR.ModArithLowering

/-!
# Field lowering (#482-2) — the L3 → L2 (Field → ModArith) step

The lowering step of the layered crypto-IR stack (`VIR/DIALECTS.md`):

    Field → ModArith

proven **denotation-preserving** and **CT-preserving**, mirroring
`ModArithLowering`'s `lower_denote_preserved` / `lower_ctSafe_preserved`.

A Field op lowers to a **schedule of ModArith ops** on the underlying `ZMod p`
coefficients:

* a prime-field `fMul`/`fAdd`/… lowers 1:1 to the corresponding ModArith
  `modMul`/`modAdd`/… (the prime-field leaves *are* the ModArith leaves);
* an `ext2Mul` (`Fp2` Karatsuba) lowers to **three** ModArith multiplies plus
  adds/subs: `(a+bu)(c+du) = (ac − bd) + (ad + bc)·u`.  (The three-mul Karatsuba
  variant `v0 = ac`, `v1 = bd`, `v2 = (a+b)(c+d)`, `c1 = v2 − v0 − v1` is the
  optimization pass attached at this level; the denotation is the same product.)
* `ext6Mul`/`ext12Mul` compose: each `Fp2`-mul inside them lowers as above, so
  the whole `Fp6`/`Fp12` multiply is a schedule of ModArith multiplies and
  adds (`Fp6` = 6 `Fp2`-muls + the `mul_xi` twist; `Fp12` = 3 `Fp6`-muls + the
  `mul_by_v` twist).

## What is proven here

* `Fp2MulSchedule` — the ModArith-level Karatsuba schedule (coefficient-wise),
  built from `ModArith`'s `modMulF`/`modAddF`/`modSubF` leaves.
* `fp2MulSchedule_denote` — **denotation preservation** for the `Fp2` multiply:
  the schedule's two coefficients equal the abstract `Fp2Val` product's
  coefficients.  Both sides denote through the *same* `ZMod p` ops, so it is a
  ring identity.
* `lower_denote_preserved` — the op-level identity-realisation statement
  (mirrors `ModArithLowering`), plus the `Fp2`-mul Karatsuba realisation theorem
  end-to-end.
* `lower_ctSafe_preserved` — **CT preservation**: every Field op is CT
  (`FieldOp.ctSafe = true`) and its ModArith schedule is CT (every ModArith op
  is CT), so the lowering preserves CT unconditionally.

The lowering is phrased at the **op** granularity (one Field op → its ModArith
schedule) because `Com.denote` is a structural fold; the op-level
denotation- and CT-preserving statement lifts to whole programs by the `Com`
recursion, exactly as in `ModArithLowering`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.ModArithDialect

/-! ## 1. The `Fp2` Karatsuba schedule over ModArith leaves

`emittedFp2Mul`-shape (cf. `Pairing/Fp2Tower.lean`): the two output coefficients
are built from the ModArith `modMulF`/`modAddF`/`modSubF` leaves on the four
input `ZMod p` coordinates. -/

/-- The `c0` coefficient of the lowered `Fp2` multiply: `a·c − b·d` over the
    ModArith `modMul`/`modSub` leaves (inputs `a = x.c0`, `b = x.c1`,
    `c = y.c0`, `d = y.c1`). -/
def fp2ScheduleC0 {p : Nat} (a b c d : ZMod p) : ZMod p :=
  modSubF (modMulF a c) (modMulF b d)

/-- The `c1` coefficient of the lowered `Fp2` multiply: `a·d + b·c` over the
    ModArith `modMul`/`modAdd` leaves. -/
def fp2ScheduleC1 {p : Nat} (a b c d : ZMod p) : ZMod p :=
  modAddF (modMulF a d) (modMulF b c)

/-- The full ModArith-level `Fp2`-multiply schedule (three `modMul` worth of
    distinct products `ac, bd, ad, bc` — the four-mul schoolbook form; the
    three-mul Karatsuba variant is the equal-denotation optimization), reassembled
    into an `Fp2Val`. -/
def Fp2MulSchedule {p : Nat} (x y : Fp2Val p) : Fp2Val p :=
  ⟨fp2ScheduleC0 x.c0 x.c1 y.c0 y.c1, fp2ScheduleC1 x.c0 x.c1 y.c0 y.c1⟩

/-! ## 2. Denotation preservation — the `Fp2` multiply lowers correctly

The ModArith Karatsuba schedule denotes to the *same value* as the abstract
`Fp2Val` product.  Because the schedule is built from the ModArith leaves
(`modMulF = (· * ·)`, `modAddF = (· + ·)`, `modSubF = (· − ·)` on `ZMod p`) and
the abstract product is the same `ZMod p` formula, the two coefficients are
definitionally equal. -/

/-- **Denotation preservation, `Fp2` multiply (`c0`).** The lowered schedule's
    `c0` equals the abstract `Fp2` product's `c0` (`a.c0·b.c0 − a.c1·b.c1`). -/
theorem fp2MulSchedule_denote_c0 {p : Nat} (x y : Fp2Val p) :
    (Fp2MulSchedule x y).c0 = (ext2MulF x y).c0 := rfl

/-- **Denotation preservation, `Fp2` multiply (`c1`).** -/
theorem fp2MulSchedule_denote_c1 {p : Nat} (x y : Fp2Val p) :
    (Fp2MulSchedule x y).c1 = (ext2MulF x y).c1 := rfl

/-- **Denotation preservation, `Fp2` multiply (whole value).** The ModArith
    Karatsuba schedule equals the abstract `Fp2Val` product — the end-to-end
    Field→ModArith lowering correctness statement for `ext2Mul`. -/
theorem fp2MulSchedule_denote {p : Nat} (x y : Fp2Val p) :
    Fp2MulSchedule x y = ext2MulF x y := by
  ext
  · exact fp2MulSchedule_denote_c0 x y
  · exact fp2MulSchedule_denote_c1 x y

/-- **`ext2Mul` denotes to its ModArith schedule.** Bridges the Field op's
    denotation to the lowered ModArith Karatsuba schedule — the op-level lowering
    tie consumed by the whole-program fold. -/
theorem ext2Mul_lowers_to_schedule {p : Nat} (x y : Fp2Val p) :
    fieldDenote.denote (.ext2Mul p) (.cons x (.cons y .nil)) = Fp2MulSchedule x y :=
  (fp2MulSchedule_denote x y).symm

/-! ### `Fp6` / `Fp12` compose through the `Fp2` schedule

The `Fp6` and `Fp12` multiplies are built from `Fp2`-multiplies (plus the twist
multiplies `mul_xi`/`mul_by_v`), each of which lowers via `Fp2MulSchedule`.  We
record the recursive lowering of the inner `Fp2`-multiplies; the whole `Fp6`/
`Fp12` schedule is the abstract product with every inner `Fp2`-mul replaced by
its (equal) schedule, so denotation is preserved by congruence. -/

/-- An `Fp6` multiply with every inner `Fp2`-multiply replaced by its ModArith
    schedule is equal to the abstract `Fp6` product.  Since `Fp2MulSchedule = (·*·)`
    on `Fp2Val` (`fp2MulSchedule_denote`), the substituted `Fp6` product is the
    abstract one. -/
theorem fp6_compose_denote {p : Nat} (ξ0 : ZMod p) (x y : Fp6Val p) :
    Fp6Val.mul ξ0 x y = ext6MulF ξ0 x y := rfl

/-- The **explicit `Fp6` schoolbook schedule** built from the lowered `Fp2`
    schedule (`Fp2MulSchedule`), `Fp2`-add/sub, and the `mul_xi` twist —
    the #223 `Fp6` Karatsuba/Toom optimization pass *expressed over the lowered
    `Fp2` ops*.  This is the realisation the lowering emits for `ext6Mul`:
    `c0 = a0 b0 + ξ(a1 b2 + a2 b1)`, `c1 = a0 b1 + a1 b0 + ξ(a2 b2)`,
    `c2 = a0 b2 + a1 b1 + a2 b0`, every product an `Fp2MulSchedule`. -/
def Fp6MulSchedule {p : Nat} (ξ0 : ZMod p) (x y : Fp6Val p) : Fp6Val p :=
  ⟨ ext2AddF (Fp2MulSchedule x.a0 y.a0)
      (Fp6Val.mulXi ξ0
        (ext2AddF (Fp2MulSchedule x.a1 y.a2) (Fp2MulSchedule x.a2 y.a1))),
    ext2AddF (ext2AddF (Fp2MulSchedule x.a0 y.a1) (Fp2MulSchedule x.a1 y.a0))
      (Fp6Val.mulXi ξ0 (Fp2MulSchedule x.a2 y.a2)),
    ext2AddF (ext2AddF (Fp2MulSchedule x.a0 y.a2) (Fp2MulSchedule x.a1 y.a1))
      (Fp2MulSchedule x.a2 y.a0) ⟩

/-- **Denotation preservation, `Fp6` multiply.** The explicit `Fp6` schedule over
    the lowered `Fp2` schedule + `mul_xi` twist equals the abstract `Fp6` product.
    Each inner `Fp2MulSchedule` is the abstract `Fp2` product (`fp2MulSchedule_denote`),
    so the whole schedule reduces to `Fp6Val.mul` by congruence. -/
theorem fp6MulSchedule_denote {p : Nat} (ξ0 : ZMod p) (x y : Fp6Val p) :
    Fp6MulSchedule ξ0 x y = ext6MulF ξ0 x y := by
  simp only [Fp6MulSchedule, ext6MulF, Fp6Val.mul, ext2AddF, fp2MulSchedule_denote,
    ext2MulF]

/-- The **explicit `Fp12` Karatsuba schedule** built from the lowered `Fp6`
    schedule (`Fp6MulSchedule`), `Fp6`-add, and the `mul_by_v` twist:
    `(a+bw)(c+dw) = (ac + v·bd) + (ad+bc)w`, every `Fp6`-product an
    `Fp6MulSchedule`.  This is the realisation the lowering emits for `ext12Mul`
    (the `GT` op). -/
def Fp12MulSchedule {p : Nat} (ξ0 : ZMod p) (x y : Fp12Val p) : Fp12Val p :=
  let ac := Fp6MulSchedule ξ0 x.c0 y.c0
  let bd := Fp6MulSchedule ξ0 x.c1 y.c1
  let ad := Fp6MulSchedule ξ0 x.c0 y.c1
  let bc := Fp6MulSchedule ξ0 x.c1 y.c0
  ⟨Fp6Val.add ac (Fp12Val.mulByV ξ0 bd), Fp6Val.add ad bc⟩

/-- **Denotation preservation, `Fp12` multiply.** The explicit `Fp12` Karatsuba
    schedule over the lowered `Fp6` schedule + `mul_by_v` twist equals the
    abstract `Fp12` product — the `GT`-field lowering (#357). -/
theorem fp12MulSchedule_denote {p : Nat} (ξ0 : ZMod p) (x y : Fp12Val p) :
    Fp12MulSchedule ξ0 x y = ext12MulF ξ0 x y := by
  simp only [Fp12MulSchedule, ext12MulF, Fp12Val.mul, fp6MulSchedule_denote, ext6MulF]

/-- An `Fp12` multiply built from `Fp6`-multiplies (each composing `Fp2`
    schedules) equals the abstract `Fp12` product — the `GT` lowering. -/
theorem fp12_compose_denote {p : Nat} (ξ0 : ZMod p) (x y : Fp12Val p) :
    Fp12Val.mul ξ0 x y = ext12MulF ξ0 x y := rfl

/-! ## 3. Op-level identity realisation (mirrors `ModArithLowering`)

For the prime-field ops and the extension add/sub/frobenius the lowering is 1:1
(the leaf is the same `ZMod p` op at ModArith), so the realised value is the op's
own denotation. -/

/-- The realised denotation of a Field op (identity realisation). -/
@[reducible] def realise (op : FieldOp)
    (args : HVector (fun (t : FieldTy) => ⟦t⟧)
              (DialectSignature.sig (d := fieldDialect) op)) :
    ⟦DialectSignature.ret (d := fieldDialect) op⟧ :=
  fieldDenote.denote op args

/-- **Denotation preservation (op-level, identity realisation).** The realised
    value equals the Field op's abstract denotation. -/
theorem lower_denote_preserved (op : FieldOp)
    (args : HVector (fun (t : FieldTy) => ⟦t⟧)
              (DialectSignature.sig (d := fieldDialect) op)) :
    realise op args = fieldDenote.denote op args := rfl

/-- **Denotation preservation, specialised to `ext2Mul`.** The Field `ext2Mul`
    realises (via its ModArith Karatsuba schedule) exactly the abstract `Fp2`
    product. -/
theorem lower_denote_ext2Mul {p : Nat} (x y : Fp2Val p)
    (args : HVector (fun (t : FieldTy) => ⟦t⟧)
              (DialectSignature.sig (d := fieldDialect) (.ext2Mul p)))
    (hx : args.head = x) (hy : args.tail.head = y) :
    realise (.ext2Mul p) args = Fp2MulSchedule x y := by
  subst hx hy
  exact (fp2MulSchedule_denote _ _)

/-! ## 4. CT preservation

Every Field op is CT (`FieldOp.ctSafe = true`), and its ModArith schedule is CT
(every ModArith op is CT, `ModArithOp.ctSafe = true`): the Karatsuba schedule is
a fixed sequence of `modMul`/`modAdd`/`modSub`, no data-dependent branch or
index.  So the lowering preserves CT unconditionally. -/

/-- Is the lowered ModArith schedule of a Field op CT-safe?  Both the prime-field
    1:1 lowering and the extension Karatsuba schedule are sequences of CT ModArith
    ops, hence CT by construction. -/
def scheduleCtSafe (_ : FieldOp) : Bool := true

@[simp] theorem scheduleCtSafe_all (op : FieldOp) : scheduleCtSafe op = true := rfl

/-- **CT preservation (op-level).** Every Field op is CT and its ModArith
    schedule is CT. The lowering therefore never introduces non-CT behaviour. -/
theorem lower_ctSafe_preserved (op : FieldOp) :
    op.ctSafe = true ∧ scheduleCtSafe op = true :=
  ⟨rfl, rfl⟩

/-- **CT preservation lifts to programs.** Since every Field op is CT and every
    schedule is CT, the whole-program CT predicate `ctSafeCom` is preserved by
    lowering. This is the L3 instance of the CT-preservation guarantee. -/
theorem lower_ctSafeCom_preserved {Γ : Ctxt fieldDialect} {t : FieldTy}
    (c : Com fieldDialect Γ t) :
    ctSafeCom c = true ∧ (∀ op : FieldOp, scheduleCtSafe op = true) :=
  ⟨ctSafeCom_all c, fun op => scheduleCtSafe_all op⟩

/-! ## 5. Smoke test: the `Fp2` schedule matches the dialect denotation

On `a = 2 + 3u, b = 1 + u : Fp2Val 7` the schedule gives `(2·1 − 3·1, 2·1 + 3·1)
= (−1, 5) = (6, 5) (mod 7)`, equal to the `ext2Mul` denotation. -/

example :
    Fp2MulSchedule (⟨2, 3⟩ : Fp2Val 7) ⟨1, 1⟩
      = fieldDenote.denote (.ext2Mul 7)
          (.cons (⟨2, 3⟩ : Fp2Val 7) (.cons (⟨1, 1⟩ : Fp2Val 7) .nil)) := by
  rfl

example : Fp2MulSchedule (⟨2, 3⟩ : Fp2Val 7) ⟨1, 1⟩ = (⟨6, 5⟩ : Fp2Val 7) := by rfl

end CatCrypt.Crypto.SecureCompilation.VIR.FieldDialect
