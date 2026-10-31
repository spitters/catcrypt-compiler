/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg
public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChainPre
public import CatCrypt.Crypto.SecureCompilation.Haxc.FieldRouteNarrow
public import CatCrypt.Crypto.Hax.NFToCatCall

/-!
# Montgomery representatives of degree `k` inside a program of `jasminDialect`

For a modulus `p` with `mont32Cert p`, `montify` rewrites a program of
`NFProg jasminDialect` whose field calls are tagged heads (`Hax.FieldTag.fieldTag?`) so that
a word may hold a field value `x` at a degree `k : ℤ`, as the canonical representative
`encK h k x` of `x · Rᵏ`, `R = 2³² mod p`. A multiplication or a squaring at `p` becomes a
call of the reduce-multiply head `montHead p`, which maps operands at degrees `k` and `j` to
the product at degree `k + j − 1`; addition, subtraction, negation and doubling keep their
heads, and act at every degree on operands of one degree. Every other binding, every
argument of a call that is no field call at `p`, every value carried by a loop or returned
by a branch, and every returned value is at degree `0`, that is, the value itself. A word
parameter may be held at a degree `d` from the entry on: it is converted once before the
program (`entryConv`).

The degree at which a definition is kept is an untrusted input `DegHint`, mirroring the
shape of the program, and the degrees of the parameters an untrusted list. When the degree
of a defined word differs from its hint, a conversion follows the definition: the
reduce-multiply by the constant `R^(k' − k + 1)`, which moves a word from degree `k` to
degree `k'`. The rewriter refuses (returns `none`) when a degree constraint fails, so the
Boolean `montifyCert` is the check of the hint.

The rewritten program runs at `montEnv E'`, which answers the reduce-multiply heads
(`montTag?`, a tag that `fieldTag?` rejects) by `MontDeg.redcMulW` and every other name by
`E'`. At `E' = fieldEnv E`, a leakage run of the source program is matched by a leakage run
of the rewritten program to the same results and events (`montify_leakSound`), at a leakage
model whose register constants are quiet; the conversions emit no event and a call emits
none. The inlining library `montLibJ` replaces a reduce-multiply call by the block
`MontDeg.redcMulBlk`.

The section `0` holds the tagged field calls in `jasminDialect` that the chain
`extChain` and the rewriter share: the signatures of the methods and the call environment
`fieldEnv` with the tagged heads answered by the `u64` table.

## Main definitions

* `fieldJSig`, `fieldNats`, `fieldEnv` — the signature of a method in `jasminDialect`, the
  numbers of its arguments, and the call environment with the tagged heads answered by the
  `u64` table.
* `montHead`, `montTag?` — the reduce-multiply head at a modulus and its recogniser.
* `montEnv` — the call environment of the reduce-multiply heads; `redcMulProg` the block
  `MontDeg.redcMulBlk` as a program, with the same denotation; `montLibJ` the inlining
  library of the reduce-multiply heads.
* `Rd`, `MRen`, `MAgree` — readings of source variables, renamings to readings and their
  agreement with valuations.
* `DegHint` — the untrusted degree assignment.
* `wordAt?`, `paramDegs`, `entryConv` — the word parameter at an index, the word parameters
  at nonzero degrees, and their conversions at entry.
* `montifyAux`, `montify`, `montifyCert` — the rewriter, at the parameter degrees from the
  identity renaming, and its certificate.

## Main results

* `fieldTag?_of_montTag?` — `fieldTag?` rejects a reduce-multiply head.
* `redcMulProg_denoteAt` — the program of the reduce-multiply block answers as `montEnv`.
* `montLibJ_sound`, `montLibJ_leakSound` — the library is sound at `montEnv E` for the
  denotation and for the leakage run with no event.
* `montifyAux_leakSound`, `entryConv_leakSound`, `montify_leakSound` — the rewritten program
  has the leakage run of the source program.
* `montify_sound`, `montifyCert_sound` — the rewritten program returns the result of the
  source program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (canonEnc w64 eq_canonEnc_of_toNat)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldArm fieldVal fieldArgs fieldVal_lt
  fieldHeadB)
open Ctxt (Var Valuation)

/-! ## 0. The tagged field calls in `jasminDialect` -/

/-- The signature in `jasminDialect` of a method of the prime-field interface: two `64`-bit
    registers for a method with two arguments, one for a method with one. -/
def fieldJSig : FieldMethod → List JasminTy
  | .add | .sub | .mul => [w64, w64]
  | .neg | .square | .double => [w64]

/-- The numbers a valuation at the signature of a method holds: its first and its second
    argument, and `0` as the second number of a method with one argument. -/
def fieldNats : (m : FieldMethod) → Valuation (d := jasminDialect) (fieldJSig m) → Nat × Nat
  | .add, .cons a (.cons b .nil) | .sub, .cons a (.cons b .nil)
  | .mul, .cons a (.cons b .nil) => (a.toNat, b.toNat)
  | .neg, .cons a .nil | .square, .cons a .nil | .double, .cons a .nil => (a.toNat, 0)

/-- The source values of a valuation at the signature of a method are the arguments
    `fieldArgs` of its numbers. -/
theorem denVals_fieldNats (m : FieldMethod) (x : Valuation (d := jasminDialect) (fieldJSig m)) :
    denVals x = fieldArgs m (fieldNats m x).1 (fieldNats m x).2 := by
  cases m <;> rcases x with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> rfl

/-- `dec` reads an integer below `2⁶⁴` as the `64`-bit word of the integer. -/
theorem dec_word64 (v : Nat) (hv : v < 2 ^ 64) :
    dec (.word 64) (.int (v : Int)) = some (BitVec.ofNat 64 v) := by
  simp only [dec]
  rw [ite_eq_left (by omega)]
  simp

/-- **The `u64` table at a tagged head.** When the call environment read off the `u64` table
    answers the tagged head of `m` at `p < 2⁶⁴` on a valuation at the signature of `m`, the
    numbers of the valuation are below `p` and the result is the canonical representative
    of `fieldVal m p` of the numbers. -/
theorem tableEnv_field {p : Nat} [NeZero p] (hp : p < 2 ^ 64) {f : String} {m : FieldMethod}
    (ht : fieldTag? f = some (m, p)) (x : Valuation (d := jasminDialect) (fieldJSig m))
    (y : Valuation (d := jasminDialect) [w64])
    (hy : (tableEnv _root_.Hax.hax64Builtins).call f (fieldJSig m) [w64] x = some y) :
    (fieldNats m x).1 < p ∧ (m.binary = true → (fieldNats m x).2 < p) ∧
      y = .cons (canonEnc p
        ((fieldVal m p (fieldNats m x).1 (fieldNats m x).2 : Nat) : ZMod p)) .nil := by
  change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
      (dec (.word 64) v).map fun z => (HVector.cons z .nil : Valuation (d := jasminDialect) [w64]))
      = some y at hy
  rw [denVals_fieldNats, _root_.Hax.hax64Builtins_fieldArgs ht hp] at hy
  unfold fieldArm at hy
  split at hy
  · rename_i hc
    refine ⟨hc.1, hc.2, ?_⟩
    have hv := fieldVal_lt m (Nat.pos_of_neZero p) (fieldNats m x).1 (fieldNats m x).2
    rw [Option.bind_some, dec_word64 _ (by omega), Option.map_some] at hy
    cases hy
    congr 1
    apply eq_canonEnc_of_toNat hp.le
    rw [BitVec.toNat_ofNat, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hv]
  · cases hy

/-- **The call environment with the field heads answered by the `u64` table**: a field head
    (`fieldHeadB`, a canonical or a Montgomery head) is answered by the environment read off
    `Hax.hax64Builtins`, every other name by `E`. -/
def fieldEnv (E : CallEnv jasminDialect) : CallEnv jasminDialect where
  call f as rs x :=
    if fieldHeadB f then (tableEnv _root_.Hax.hax64Builtins).call f as rs x
    else E.call f as rs x

/-- `fieldEnv E` answers a field head by the `u64` table. -/
theorem fieldEnv_of_fieldHeadB (E : CallEnv jasminDialect) {f : String}
    (h : fieldHeadB f = true) (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as) :
    (fieldEnv E).call f as rs x = (tableEnv _root_.Hax.hax64Builtins).call f as rs x :=
  ite_eq_left h

/-- `fieldEnv E` answers a tagged head by the `u64` table. -/
theorem fieldEnv_of_isSome (E : CallEnv jasminDialect) {f : String}
    (h : (fieldTag? f).isSome = true) (as rs : List JasminTy)
    (x : Valuation (d := jasminDialect) as) :
    (fieldEnv E).call f as rs x = (tableEnv _root_.Hax.hax64Builtins).call f as rs x :=
  fieldEnv_of_fieldHeadB E (by simp [fieldHeadB, h]) as rs x

/-- `fieldEnv E` answers a Montgomery head by the `u64` table, whose value at the head is
    `Hax.FieldTag.fieldCallMont` (`Hax.hax64Builtins_of_fieldTagM?`). -/
theorem fieldEnv_of_fieldTagM? (E : CallEnv jasminDialect) {f : String}
    {m : FieldMethod} {p k : Nat} (h : _root_.Hax.FieldTag.fieldTagM? f = some (m, p, k))
    (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as) :
    (fieldEnv E).call f as rs x = (tableEnv _root_.Hax.hax64Builtins).call f as rs x :=
  fieldEnv_of_fieldHeadB E (_root_.Hax.FieldTag.fieldHeadB_of_fieldTagM? h) as rs x

/-- `fieldEnv E` answers a name that is no field head by `E`. -/
theorem fieldEnv_of_none (E : CallEnv jasminDialect) {f : String} (h : fieldHeadB f = false)
    (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as) :
    (fieldEnv E).call f as rs x = E.call f as rs x :=
  ite_eq_right (by simp [h])

/-- The embedding of a straight-line program has no `call`. -/
theorem callFree_ofCom {d : Dialect.{0, 0}} [DialectSignature d] [TyDenote d.Ty] [HasWord64 d]
    [HasBoolBit d] : ∀ {Γ : Ctxt d} {t : d.Ty} (c : Com d Γ t), (NFProg.ofCom c).callFree = true
  | _, _, .ret _ => rfl
  | _, _, .var _ k => callFree_ofCom k

end CatCrypt.Crypto.SecureCompilation.Haxc

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering (hvAppend)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord (canonEnc w64 eq_canonEnc_of_toNat
  canonEnc_toNat)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.Mont32 (mont32Cert mont32Cert_spec)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldWord.MontDeg (R32 encK encK_zero redcMulW
  redcMulW_encK neZero_of_cert redcMulBlk redcMulBlk_value opsQuiet_redcMulBlk)
open CatCrypt.Crypto.SecureCompilation.VIR.ComLevelCheck (LeakModel LeakKind opLeak)
open CatCrypt.Crypto.SecureCompilation.CT (CTLeak)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (eConst)
open CatCrypt.Crypto.Hax.ImpToNF (dec)
open _root_.Hax.FieldTag (FieldMethod fieldTag? fieldTagChars? fieldHead fieldArm fieldVal
  fieldVal_lt splitTag fieldHeadB)
open Ctxt (Var Valuation)

/-! ## 1. The reduce-multiply head and its environment -/

/-- **The reduce-multiply head at `p`**: `redc` before the tagged head of the multiplication
    at `p`. -/
def montHead (p : Nat) : String := "redc" ++ fieldHead .mul p

/-- **The modulus of a reduce-multiply head**: for a name `redc` followed by the tagged head
    of the multiplication at `q`, the modulus `q`. -/
def montTag? (f : String) : Option Nat :=
  match f.toList with
  | 'r' :: 'e' :: 'd' :: 'c' :: cs =>
      match fieldTagChars? cs with
      | some (.mul, q) => some q
      | _ => none
  | _ => none

/-- **`fieldTag?` rejects a reduce-multiply head**: no method is named by characters that
    begin with `r`. -/
theorem fieldTag?_of_montTag? {f : String} {q : Nat} (hf : montTag? f = some q) :
    fieldTag? f = none := by
  unfold montTag? at hf
  split at hf
  · rename_i cs hcs
    unfold fieldTag? _root_.Hax.FieldTag.fieldTagChars?
    rw [hcs]
    split
    · rfl
    · rfl
  · cases hf

/-- **A reduce-multiply head is no field head**: neither `fieldTag?` nor `fieldTagM?` reads
    a name that begins with `r`. -/
theorem fieldHeadB_of_montTag? {f : String} {q : Nat} (hf : montTag? f = some q) :
    fieldHeadB f = false := by
  refine _root_.Hax.FieldTag.fieldHeadB_eq_false_iff.mpr ⟨fieldTag?_of_montTag? hf, ?_⟩
  unfold montTag? at hf
  split at hf
  · rename_i cs hcs
    unfold _root_.Hax.FieldTag.fieldTagM? _root_.Hax.FieldTag.fieldTagMChars?
    rw [hcs]
    simp [Hax.FieldTag.splitMontTag, fieldTagChars?, splitTag, FieldMethod.ofChars?,
      FieldMethod.nameChars]
  · cases hf

/-- The value of the reduce-multiply call at `q` on two words, and no value at any other
    signature. -/
def montCall (q : Nat) : (as rs : List JasminTy) → Valuation (d := jasminDialect) as →
    Option (Valuation (d := jasminDialect) rs)
  | [.reg 64, .reg 64], [.reg 64], .cons a (.cons b .nil) => some (.cons (redcMulW q a b) .nil)
  | _, _, _ => none

/-- **The call environment of the reduce-multiply heads**: a head `montTag?` reads at the
    modulus `q` is answered by `MontDeg.redcMulW q` on two words, every other name by `E`. -/
def montEnv (E : CallEnv jasminDialect) : CallEnv jasminDialect where
  call f as rs x :=
    match montTag? f with
    | some q => montCall q as rs x
    | none => E.call f as rs x

theorem montEnv_of_none (E : CallEnv jasminDialect) {f : String} (hf : montTag? f = none)
    (as rs : List JasminTy) (x : Valuation (d := jasminDialect) as) :
    (montEnv E).call f as rs x = E.call f as rs x := by
  simp only [montEnv, hf]

theorem montEnv_montHead (E : CallEnv jasminDialect) {p : Nat} (hm : montTag? (montHead p) = some p)
    (a b : BitVec 64) :
    (montEnv E).call (montHead p) [w64, w64] [w64] (.cons a (.cons b .nil)) =
      some (.cons (redcMulW p a b) .nil) := by
  simp only [montEnv, hm]
  rfl

/-- **The reduce-multiply block as a program** on its two parameters. -/
def redcMulProg (p : Nat) : NFProg jasminDialect [w64, w64] [w64] :=
  NFProg.ofCom (redcMulBlk p .here (.there .here))

/-- **The program of the reduce-multiply block answers as `montEnv`**: at every call
    environment and fuel it returns `redcMulW p` of its parameters. -/
theorem redcMulProg_denoteAt (p : Nat) (E : CallEnv jasminDialect) (fuel : Nat)
    (a b : BitVec 64) :
    (redcMulProg p).denoteAt E fuel (.cons a (.cons b .nil)) =
      montCall p [w64, w64] [w64] (.cons a (.cons b .nil)) := by
  unfold NFProg.denoteAt redcMulProg
  let _ : CallDenote jasminDialect := ⟨E⟩
  refine (NFProg.denote_ofCom (d := jasminDialect) _ fuel _).trans ?_
  rw [redcMulBlk_value]
  rfl

/-- **The body of a reduce-multiply head** at the signature `as → rs`: at two words with one
    word result, the program `redcMulProg q` of the modulus `q` the head names; `none`
    otherwise. -/
def montBody (f : String) (as rs : List JasminTy) : Option (NFProg jasminDialect as rs) :=
  match montTag? f with
  | some q =>
      if hs : as = [w64, w64] ∧ rs = [w64] then some (hs.1 ▸ hs.2 ▸ redcMulProg q) else none
  | none => none

/-- **The inlining library of the reduce-multiply heads**: no operation has a body, and a
    `call` of a reduce-multiply head has the body `montBody`. -/
def montLibJ : InlineLib jasminDialect where
  op _ := none
  call := montBody

/-- **The library of the reduce-multiply heads is sound at `montEnv E`**, at every fuel: a
    head is answered by `montCall`, and the program `redcMulProg` of its modulus returns the
    same value (`redcMulProg_denoteAt`). -/
theorem montLibJ_sound (E : CallEnv jasminDialect) (fuel : Nat) :
    @InlineLib.Sound jasminDialect _ _ _ _ _ ⟨montEnv E⟩ montLibJ fuel := by
  refine @InlineLib.Sound.mk jasminDialect _ _ _ _ _ ⟨montEnv E⟩ montLibJ fuel
    (fun o b hb => by cases hb) ?_
  intro f as rs b hb x y hy
  change montBody f as rs = some b at hb
  change (montEnv E).call f as rs x = some y at hy
  unfold montBody at hb
  split at hb
  · rename_i q hq
    split at hb
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      cases hb
      simp only [montEnv, hq] at hy
      rcases x with _ | ⟨a, _ | ⟨c, _ | _⟩⟩
      change (redcMulProg q).denoteAt (montEnv E) fuel _ = some y
      rw [redcMulProg_denoteAt]
      exact hy
    · cases hb
  · cases hb

/-- **The library of the reduce-multiply heads is sound for the leakage run at `montEnv E`**:
    a body runs as its head (`montLibJ_sound`) and binds register constants and register
    arithmetic only (`MontDeg.opsQuiet_redcMulBlk`), at a leakage model in which these are
    quiet. -/
theorem montLibJ_leakSound (M : LeakModel jasminDialect)
    (hA : ∀ bop w, M.kind (.regArith bop w) = .quiet)
    (hK : ∀ w n, M.kind (.regConst w n) = .quiet) (E : CallEnv jasminDialect) (fuel : Nat) :
    montLibJ.LeakSound M (montEnv E) fuel := by
  refine ⟨fun o b hb => (by cases hb), ?_⟩
  intro f as rs b hb x y hy
  have hval := @InlineLib.Sound.call jasminDialect _ _ _ _ _ ⟨montEnv E⟩ montLibJ fuel
    (montLibJ_sound E fuel) f as rs b hb x y hy
  change b.denoteAt (montEnv E) fuel x = some y at hval
  rw [← Dialects.NFLeak.NFProg.leakRunMC_fst M (montEnv E) fuel b x] at hval
  have hev : (Dialects.NFLeak.NFProg.leakRunMC M (montEnv E) fuel b x).map Prod.snd =
      some [] := by
    change montBody f as rs = some b at hb
    unfold montBody at hb
    split at hb
    · rename_i q _
      split at hb
      · rename_i hs
        obtain ⟨rfl, rfl⟩ := hs
        cases hb
        have hcf : (redcMulProg q).callFree = true := callFree_ofCom _
        rw [Dialects.NFLeak.NFProg.leakRunMC_of_callFree M _ fuel _ hcf]
        exact congrArg (Option.map Prod.snd)
          (Dialects.NFLeak.NFProg.leakRunM_ofCom_quiet M fuel _
            (opsQuiet_redcMulBlk M (fun bop w _ => hA bop w) hK q _ _) x)
      · cases hb
    · cases hb
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hval
  rw [hr, Option.map_some, Option.some.injEq] at hev
  rw [hr, ← hev]

/-! ## 2. Field values of the tagged heads -/

/-- The operation of `ZMod p` a method computes on its arguments; a method with one argument
    does not read the second. -/
def fieldOp {p : Nat} : FieldMethod → ZMod p → ZMod p → ZMod p
  | .add, u, v => u + v
  | .sub, u, v => u - v
  | .mul, u, v => u * v
  | .neg, u, _ => -u
  | .square, u, _ => u * u
  | .double, u, _ => u + u

/-- The methods that commute with the multiplication by a constant: addition, subtraction,
    negation and doubling. -/
def linB : FieldMethod → Bool
  | .add | .sub | .neg | .double => true
  | .mul | .square => false

/-- The value of a method on canonical representatives is the operation of `ZMod p`. -/
theorem fieldVal_cast {p : Nat} [NeZero p] (m : FieldMethod) (u v : ZMod p) :
    ((fieldVal m p u.val v.val : Nat) : ZMod p) = fieldOp m u v := by
  have hv := ZMod.val_lt v
  have hu := ZMod.val_lt u
  cases m <;> simp only [fieldVal, fieldOp, ZMod.natCast_mod]
  · push_cast; simp
  · rw [Nat.cast_sub (by omega)]; push_cast; simp
  · push_cast; simp
  · rw [Nat.cast_sub hu.le]; simp
  · push_cast; simp
  · push_cast; simp [two_mul]

/-- A method that commutes with the multiplication by `c`, or `c = 1`, scales its value
    by `c`. -/
theorem fieldOp_mul_right {p : Nat} (m : FieldMethod) (u v c : ZMod p)
    (hm : linB m = true ∨ c = 1) : fieldOp m (u * c) (v * c) = fieldOp m u v * c := by
  rcases hm with hm | rfl
  · cases m <;> simp [linB] at hm <;> simp only [fieldOp] <;> ring
  · simp

/-- **The `u64` table at a tagged head on canonical arguments**: at `p < 2⁶⁴`, on a valuation
    whose numbers are below `p`, the table answers the canonical representative of
    `fieldVal m p` of the numbers. -/
theorem tableEnv_field_some {p : Nat} [NeZero p] (hp : p < 2 ^ 64) {f : String}
    {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (x : Valuation (d := jasminDialect) (fieldJSig m)) (ha : (fieldNats m x).1 < p)
    (hb : m.binary = true → (fieldNats m x).2 < p) :
    (tableEnv _root_.Hax.hax64Builtins).call f (fieldJSig m) [w64] x =
      some (.cons (canonEnc p
        ((fieldVal m p (fieldNats m x).1 (fieldNats m x).2 : Nat) : ZMod p)) .nil) := by
  change ((_root_.Hax.hax64Builtins f (denVals x)).bind fun v =>
      (dec (.word 64) v).map fun z => (HVector.cons z .nil : Valuation (d := jasminDialect) [w64]))
      = _
  rw [denVals_fieldNats, _root_.Hax.hax64Builtins_fieldArgs ht hp]
  unfold fieldArm
  rw [ite_eq_left ⟨ha, hb⟩]
  have hv := fieldVal_lt m (Nat.pos_of_neZero p) (fieldNats m x).1 (fieldNats m x).2
  rw [Option.bind_some, dec_word64 _ (by omega), Option.map_some]
  congr 2
  apply eq_canonEnc_of_toNat hp.le
  rw [BitVec.toNat_ofNat, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hv]

section Deg

variable {p : Nat} (h : mont32Cert p = true)
include h

theorem lt_two64_of_cert : p < 2 ^ 64 := by
  have := (mont32Cert_spec h).2.2.1; omega

/-- A word below `p` is the canonical representative of its number. -/
theorem word_eq_encK_zero (x : BitVec 64) (hx : x.toNat < p) :
    x = encK h 0 ((x.toNat : Nat) : ZMod p) := by
  have := neZero_of_cert h
  rw [encK_zero]
  apply eq_canonEnc_of_toNat (lt_two64_of_cert h).le
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]

/-- The number of the canonical representative of `z`, read in `ZMod p`, is `z`. -/
theorem cast_canonEnc (z : ZMod p) : (((canonEnc p z).toNat : Nat) : ZMod p) = z := by
  have := neZero_of_cert h
  rw [canonEnc_toNat (lt_two64_of_cert h).le, ZMod.natCast_zmod_val]

/-- The number of `encK h k z` is the number of `z · Rᵏ`. -/
theorem encK_toNat (k : ℤ) (z : ZMod p) :
    (encK h k z).toNat = (z * ↑(R32 h ^ k)).val := by
  have := neZero_of_cert h
  exact canonEnc_toNat (lt_two64_of_cert h).le _

theorem encK_toNat_lt (k : ℤ) (z : ZMod p) : (encK h k z).toNat < p := by
  have := neZero_of_cert h
  rw [encK_toNat]
  exact ZMod.val_lt _

/-- The number of a conversion constant: the canonical representative of `Rʲ`. -/
def convC (j : ℤ) : Nat := ((R32 h ^ j : (ZMod p)ˣ) : ZMod p).val

/-- The word of a conversion constant holds `1` at the degree `j`. -/
theorem convC_word (j : ℤ) : BitVec.ofNat 64 (convC h j) = encK h j 1 := by
  have := neZero_of_cert h
  have hlt : convC h j < p := ZMod.val_lt _
  have h64 := lt_two64_of_cert h
  unfold encK
  apply eq_canonEnc_of_toNat h64.le
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), one_mul]
  rfl

/-- **The reduce-multiply by a conversion constant** moves a value from degree `k` to
    degree `k + j − 1`. -/
theorem redcMulW_conv (k j : ℤ) (z : ZMod p) :
    redcMulW p (encK h k z) (BitVec.ofNat 64 (convC h j)) = encK h (k + j - 1) z := by
  rw [convC_word, redcMulW_encK, mul_one]

end Deg

/-! ## 3. Readings -/

/-- **A reading** of a source variable of type `t` in the context `Θ` of the rewritten
    program: a variable with the same value (`same`), or, at the word type, a variable that
    holds the value at the degree `k` when the value is below the modulus (`mont`). -/
inductive Rd (Θ : Ctxt jasminDialect) : JasminTy → Type where
  | same {t : JasminTy} (v : Var Θ t) : Rd Θ t
  | mont (v : Var Θ w64) (k : ℤ) : Rd Θ w64

namespace Rd

variable {Θ : Ctxt jasminDialect}

/-- The variable of a reading. -/
def var : {t : JasminTy} → Rd Θ t → Var Θ t
  | _, .same v => v
  | _, .mont v _ => v

/-- The degree of a reading; `0` for `same`. -/
def deg : {t : JasminTy} → Rd Θ t → ℤ
  | _, .same _ => 0
  | _, .mont _ k => k

/-- The variable of a reading `same`. -/
def same? : {t : JasminTy} → Rd Θ t → Option (Var Θ t)
  | _, .same v => some v
  | _, .mont _ _ => none

/-- A reading renamed along a renaming of the context. -/
def rename {Θ' : Ctxt jasminDialect} (g : Ctxt.Hom Θ Θ') : {t : JasminTy} → Rd Θ t → Rd Θ' t
  | _, .same v => .same (g v)
  | _, .mont v k => .mont (g v) k

theorem eq_of_same? {t : JasminTy} {r : Rd Θ t} {w : Var Θ t} (hr : r.same? = some w) :
    r = .same w := by
  cases r <;> simp_all [same?]

end Rd

/-- The reading of a word that holds a value below the modulus at the degree `k`: `same` at
    degree `0`. -/
def rdOf {Θ : Ctxt jasminDialect} (v : Var Θ w64) (k : ℤ) : Rd Θ w64 :=
  if k = 0 then .same v else .mont v k

section Rel

variable {p : Nat} (h : mont32Cert p = true)

/-- **The relation of a reading** at a valuation `W` of the rewritten context and a source
    value `x`: equality for `same`, and for `mont v k`, `v` holds `x` at the degree `k`
    when `x` is below `p`. -/
def Rd.rel {Θ : Ctxt jasminDialect} (W : Valuation Θ) : {t : JasminTy} → Rd Θ t → ⟦t⟧ → Prop
  | _, .same v, x => v.lookup W = x
  | _, .mont v k, x => BitVec.toNat (w := 64) x < p →
      v.lookup W = encK h k ((BitVec.toNat (w := 64) x : Nat) : ZMod p)

/-- A renaming `g` from `W` to `W'` keeps every lookup. -/
def Pres {Θ Θ' : Ctxt jasminDialect} (g : Ctxt.Hom Θ Θ') (W : Valuation Θ)
    (W' : Valuation Θ') : Prop :=
  ∀ {s : JasminTy} (v : Var Θ s), (g v).lookup W' = v.lookup W

theorem Rd.rel_rename {Θ Θ' : Ctxt jasminDialect} {g : Ctxt.Hom Θ Θ'} {W : Valuation Θ}
    {W' : Valuation Θ'} (hp : Pres g W W') {t : JasminTy} (r : Rd Θ t) (x : ⟦t⟧)
    (hr : r.rel h W x) : (r.rename g).rel h W' x := by
  cases r with
  | same v => exact (hp v).trans hr
  | mont v k => exact fun hx => (hp v).trans (hr hx)

/-- On a value below `p`, the variable of a word reading holds the value at the degree of
    the reading. -/
theorem Rd.rel_canon {Θ : Ctxt jasminDialect} {W : Valuation Θ} (r : Rd Θ w64)
    (x : BitVec 64) (hr : r.rel h W x) (hx : x.toNat < p) :
    r.var.lookup W = encK h r.deg ((x.toNat : Nat) : ZMod p) := by
  cases r with
  | same v => exact hr.trans (word_eq_encK_zero h x hx)
  | mont v k => exact hr hx

/-- A word holding `z` at the degree `k` is read by `rdOf` as the canonical representative
    of `z`. -/
theorem rdOf_rel {Θ : Ctxt jasminDialect} {W : Valuation Θ} (v : Var Θ w64) (k : ℤ)
    (z : ZMod p) (hv : v.lookup W = encK h k z) :
    (rdOf v k).rel h W (canonEnc p z) := by
  unfold rdOf
  split
  · rename_i hk
    subst hk
    change v.lookup W = canonEnc p z
    rw [hv, encK_zero]
  · intro _
    rw [cast_canonEnc h, hv]

end Rel

/-! ## 4. Renamings -/

/-- A renaming of the source variables to readings. -/
abbrev MRen (Γ Θ : Ctxt jasminDialect) : Type := ∀ {t : JasminTy}, Var Γ t → Rd Θ t

/-- The identity renaming: every variable read as itself. -/
def idRen (Γ : Ctxt jasminDialect) : MRen Γ Γ := fun v => .same v

/-- A renaming under one more binding read by `r`, the others renamed along `g`. -/
def MRen.lift {Γ Θ Θ' : Ctxt jasminDialect} (ρ : MRen Γ Θ) (g : Ctxt.Hom Θ Θ')
    {s : JasminTy} (r : Rd Θ' s) : MRen (s :: Γ) Θ'
  | _, .here => r
  | _, .there v => (ρ v).rename g

/-- A renaming under a tuple `cs`, read by the first variables as themselves. -/
def MRen.app {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) :
    (cs : List JasminTy) → MRen (cs ++ Γ) (cs ++ Θ)
  | [] => ρ
  | _ :: cs => MRen.lift (MRen.app ρ cs) (fun v => .there v) (.same .here)

/-- The renaming `ρ` with the word variable `v` read by `r`. -/
def MRen.set {Θ : Ctxt jasminDialect} : {Γ : Ctxt jasminDialect} → MRen Γ Θ → Var Γ w64 →
    Rd Θ w64 → {t : JasminTy} → Var Γ t → Rd Θ t
  | _, _, .here, r, _, .here => r
  | _, ρ, .here, _, _, .there w => ρ (.there w)
  | _, ρ, .there _, _, _, .here => ρ .here
  | _, ρ, .there v, r, _, .there w => MRen.set (fun x => ρ (.there x)) v r w

/-- The renaming `ρ` followed by the renaming `g` of the rewritten context. -/
def MRen.comp {Γ Θ Θ' : Ctxt jasminDialect} (ρ : MRen Γ Θ) (g : Ctxt.Hom Θ Θ') : MRen Γ Θ' :=
  fun v => (ρ v).rename g

/-- The variables of a vector, when every reading is `same`. -/
def sameVars {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) :
    {ts : List JasminTy} → HVector (fun t => Var Γ t) ts →
      Option (HVector (fun t => Var Θ t) ts)
  | [], .nil => some .nil
  | _ :: _, .cons v vs => (ρ v).same?.bind fun w => (sameVars ρ vs).map (.cons w)

/-- An expression on the variables of its arguments, when every reading is `same`. -/
def renExpr {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) {t : JasminTy}
    (e : Expr jasminDialect Γ t) : Option (Expr jasminDialect Θ t) :=
  (sameVars ρ e.args).map fun args => ⟨e.op, e.retTy_eq, args⟩

section Agree

variable {p : Nat} (h : mont32Cert p = true)

/-- Every variable is related to its reading. -/
def MAgree {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (X : Valuation Γ) (W : Valuation Θ) :
    Prop :=
  ∀ (t : JasminTy) (v : Var Γ t), (ρ v).rel h W (v.lookup X)

theorem idRen_agree {Γ : Ctxt jasminDialect} (X : Valuation Γ) : MAgree h (idRen Γ) X X :=
  fun _ _ => rfl

theorem MAgree.lift {Γ Θ Θ' : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) {g : Ctxt.Hom Θ Θ'} {W' : Valuation Θ'}
    (hp : Pres g W W') {s : JasminTy} (r : Rd Θ' s) (x : ⟦s⟧) (hr : r.rel h W' x) :
    MAgree h (ρ.lift g r) (X.extend x) W' := by
  intro t v
  cases v with
  | here => exact hr
  | there v => exact Rd.rel_rename h hp (ρ v) _ (hA t v)

theorem MAgree.app {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) :
    ∀ (cs : List JasminTy) (A : Valuation (d := jasminDialect) cs), MAgree h (MRen.app ρ cs) (hvAppend A X)
      (hvAppend A W)
  | [], .nil => hA
  | _ :: cs, .cons x A =>
      (MAgree.app hA cs A).lift h (g := fun v => .there v) (fun _ => rfl) (.same .here) x rfl

theorem MAgree.comp {Γ Θ Θ' : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) {g : Ctxt.Hom Θ Θ'} {W' : Valuation Θ'}
    (hp : Pres g W W') : MAgree h (ρ.comp g) X W' :=
  fun t v => Rd.rel_rename h hp (ρ v) _ (hA t v)

/-- A renaming that agrees with `X` and `W` agrees after the word variable `v` is read by a
    reading related to its value. -/
theorem MAgree.set {Θ : Ctxt jasminDialect} {W : Valuation Θ} :
    ∀ {Γ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}, MAgree h ρ X W →
      ∀ (v : Var Γ w64) (r : Rd Θ w64), r.rel h W (v.lookup X) → MAgree h (MRen.set ρ v r) X W
  | _ :: _, _, .cons _ _, _, .here, _, hr, _, .here => hr
  | _ :: _, _, .cons _ _, hA, .here, _, _, _, .there w => hA _ (.there w)
  | _ :: _, _, .cons _ _, hA, .there _, _, _, _, .here => hA _ .here
  | _ :: _, ρ, .cons _ X, hA, .there v, r, hr, _, .there w =>
      MAgree.set (ρ := fun x => ρ (.there x)) (X := X) (fun t x => hA t (.there x)) v r hr _ w

theorem sameVars_lookup {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) :
    ∀ {ts : List JasminTy} (vs : HVector (fun t => Var Γ t) ts) ws,
      sameVars ρ vs = some ws → Expr.lookupArgs ws W = Expr.lookupArgs vs X
  | [], .nil, _, hw => by
      cases hw
      rfl
  | _ :: _, .cons v vs, ws, hw => by
      obtain ⟨w, hw1, hw⟩ := Option.bind_eq_some_iff.mp hw
      obtain ⟨ws', hws', rfl⟩ := Option.map_eq_some_iff.mp hw
      have hv : (ρ v).rel h W (v.lookup X) := hA _ v
      have e : ρ v = .same w := Rd.eq_of_same? hw1
      rw [e] at hv
      show HVector.cons (w.lookup W) (Expr.lookupArgs ws' W) =
        HVector.cons (v.lookup X) (Expr.lookupArgs vs X)
      rw [show w.lookup W = v.lookup X from hv, sameVars_lookup hA vs ws' hws']

theorem renExpr_denoteM {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) {t : JasminTy} (e : Expr jasminDialect Γ t)
    (e' : Expr jasminDialect Θ t) (he : renExpr ρ e = some e') :
    e'.denoteM (M := Option) W = e.denoteM (M := Option) X := by
  obtain ⟨op, rfl, args⟩ := e
  obtain ⟨args', ha, rfl⟩ := Option.map_eq_some_iff.mp he
  simp only [Expr.denoteM_option_eq_some]
  show some (DialectDenote.denote op (Expr.lookupArgs args' W)) =
    some (DialectDenote.denote op (Expr.lookupArgs args X))
  rw [sameVars_lookup h hA args args' ha]

end Agree

/-! ## 5. The rewriter -/

/-- **The degree assignment**, mirroring the shape of a program: the degree at which the
    word of a binding (`var`) or of a field call (`call`) is kept, and the assignments of the
    regions and continuations. A missing entry is read as degree `0`. -/
inductive DegHint where
  | leaf
  | var (d : ℤ) (k : DegHint)
  | call (d : ℤ) (k : DegHint)
  | loop (body k : DegHint)
  | branch (thn els k : DegHint)

namespace DegHint

/-- The degree of the current binding. -/
def deg : DegHint → ℤ
  | var d _ => d
  | call d _ => d
  | _ => 0

/-- The assignment of the continuation. -/
def next : DegHint → DegHint
  | var _ k | call _ k | loop _ k | branch _ _ k => k
  | leaf => leaf

/-- The assignment of the loop body or of the first arm. -/
def sub1 : DegHint → DegHint
  | loop b _ => b
  | branch t _ _ => t
  | _ => leaf

/-- The assignment of the second arm. -/
def sub2 : DegHint → DegHint
  | branch _ e _ => e
  | _ => leaf

end DegHint

/-- The variable of the word parameter at the index `i` of a context; `none` when the entry at
    `i` is no word or `i` is past the end. -/
def wordAt? : (Γ : Ctxt jasminDialect) → Nat → Option (Var Γ w64)
  | .reg 64 :: _, 0 => some .here
  | _ :: _, 0 => none
  | [], _ => none
  | _ :: Γ, i + 1 => (wordAt? Γ i).map .there

/-- The word parameters of `Γ` at a nonzero degree of the list `pd`, which holds the degree of
    the parameter at each index. -/
def paramDegs (Γ : Ctxt jasminDialect) (pd : List ℤ) : List (Var Γ w64 × ℤ) :=
  (List.range Γ.length).filterMap fun i =>
    (wordAt? Γ i).bind fun v => if pd.getD i 0 = 0 then none else some (v, pd.getD i 0)

/-- No parameter is at a nonzero degree of the empty list. -/
theorem paramDegs_nil (Γ : Ctxt jasminDialect) : paramDegs Γ [] = [] := by
  simp [paramDegs]

/-- The continuation of a binding of type `t`: a renaming of the rewritten context and the
    reading of the bound value. -/
abbrev BindK (Θ : Ctxt jasminDialect) (t : JasminTy) (us : List JasminTy) : Type :=
  ∀ {Θ' : Ctxt jasminDialect}, Ctxt.Hom Θ Θ' → Rd Θ' t → Option (NFProg jasminDialect Θ' us)

/-- The continuation of a call with the results `rs`: the rewriter of the continuation at a
    renaming of the source context after the call. -/
abbrev CallK (Γ : Ctxt jasminDialect) (rs us : List JasminTy) : Type :=
  ∀ {Θ' : Ctxt jasminDialect}, MRen (rs ++ Γ) Θ' → Option (NFProg jasminDialect Θ' us)

section Rewrite

variable {p : Nat} (h : mont32Cert p = true)

/-- **A conversion** of the word `x` by the constant `Rʲ`: the binding of the constant and
    the reduce-multiply call on `x` and the constant. -/
def convProg {Θ : Ctxt jasminDialect} (x : Var Θ w64) (j : ℤ) {us : List JasminTy}
    (k : NFProg jasminDialect (w64 :: w64 :: Θ) us) : NFProg jasminDialect Θ us :=
  .var (eConst (convC h j))
    (@NFProg.call jasminDialect _ _ _ _ (w64 :: Θ) [w64, w64] [w64] us (montHead p)
      (.cons x.there (.cons .here .nil)) k)

/-- The result `v` of a field call, at the degree `k`, continued at the degree `d`: read by
    `rdOf v k` when `k = d`, and otherwise converted by `R^(d − k + 1)`. -/
def resConv {Θ : Ctxt jasminDialect} (v : Var Θ w64) (k d : ℤ) {us : List JasminTy}
    (kk : BindK Θ w64 us) : Option (NFProg jasminDialect Θ us) :=
  if k = d then kk (fun w => w) (rdOf v k)
  else (kk (fun w => .there (.there w)) (rdOf .here d)).map (convProg h v (d - k + 1))

/-- The bound word of a binding continued at the degree `d`, converted by `R^(d + 1)`; a
    binding of any other type is refused. -/
def wordConv {Θ : Ctxt jasminDialect} (d : ℤ) {us : List JasminTy} :
    {t : JasminTy} → BindK (t :: Θ) t us → Option (NFProg jasminDialect (t :: Θ) us)
  | .reg 64, kk =>
      (kk (fun w => .there (.there w)) (.mont .here d)).map (convProg h .here (d + 1))
  | _, _ => none

/-- The value of a binding continued at the degree `d`: itself at degree `0`, and otherwise
    `wordConv`. -/
def varConv {Θ : Ctxt jasminDialect} (d : ℤ) {us : List JasminTy} {t : JasminTy}
    (kk : BindK (t :: Θ) t us) : Option (NFProg jasminDialect (t :: Θ) us) :=
  if d = 0 then kk (fun w => w) (.same .here) else wordConv h d kk

/-- The continuation of a field call after its result. -/
def resK {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) {us : List JasminTy}
    (kk : CallK Γ [w64] us) : BindK (w64 :: Θ) w64 us :=
  fun g r => kk (MRen.lift ρ (fun w => g (.there w)) r)

/-- A field call of the head `g` on `args` with its result at the degree `k`, continued at
    the degree `d`. -/
def fieldRes {Γ Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (g : String) {as : List JasminTy}
    (args : HVector (fun t => Var Θ t) as) (k d : ℤ) {us : List JasminTy}
    (kk : CallK Γ [w64] us) : Option (NFProg jasminDialect Θ us) :=
  (resConv h (Θ := w64 :: Θ) .here k d (resK ρ kk)).map
    (@NFProg.call jasminDialect _ _ _ _ Θ as [w64] us g args)

/-- **A call kept as it is**, on arguments read as themselves, with its results read as
    themselves. -/
def opaqueArm {Γ Θ : Ctxt jasminDialect} (f : String) {as rs : List JasminTy}
    (args : HVector (fun t => Var Γ t) as) (ρ : MRen Γ Θ) {us : List JasminTy}
    (kk : CallK Γ rs us) : Option (NFProg jasminDialect Θ us) :=
  (sameVars ρ args).bind fun args' => (kk (MRen.app ρ rs)).map (NFProg.call f args')

/-- **A call with two word arguments.** A multiplication at `p` becomes the reduce-multiply
    at the sum of the degrees minus one, unless both degrees and the hint are `0`; an
    addition or subtraction at `p`, and a multiplication at degree `0`, keeps its head on
    operands of one degree. Any other call is kept as it is. -/
def binArm {Γ Θ : Ctxt jasminDialect} (f : String) (a b : Var Γ w64) (ρ : MRen Γ Θ) (d : ℤ)
    {us : List JasminTy} (kk : CallK Γ [w64] us) : Option (NFProg jasminDialect Θ us) :=
  match fieldTag? f with
  | some (m, q) =>
      if q = p ∧ m.binary = true then
        if m = .mul ∧ ¬((ρ a).deg = 0 ∧ (ρ b).deg = 0 ∧ d = 0) then
          fieldRes h ρ (montHead p) (.cons (ρ a).var (.cons (ρ b).var .nil))
            ((ρ a).deg + (ρ b).deg - 1) d kk
        else if (ρ a).deg = (ρ b).deg ∧ (linB m = true ∨ (ρ a).deg = 0) then
          fieldRes h ρ f (.cons (ρ a).var (.cons (ρ b).var .nil)) (ρ a).deg d kk
        else none
      else opaqueArm f (.cons a (.cons b .nil)) ρ kk
  | none => opaqueArm f (.cons a (.cons b .nil)) ρ kk

/-- **A call with one word argument.** A squaring at `p` becomes the reduce-multiply of the
    operand with itself, unless its degree and the hint are `0`; a negation or doubling at
    `p`, and a squaring at degree `0`, keeps its head. Any other call is kept as it is. -/
def unArm {Γ Θ : Ctxt jasminDialect} (f : String) (a : Var Γ w64) (ρ : MRen Γ Θ) (d : ℤ)
    {us : List JasminTy} (kk : CallK Γ [w64] us) : Option (NFProg jasminDialect Θ us) :=
  match fieldTag? f with
  | some (m, q) =>
      if q = p ∧ m.binary = false then
        if m = .square ∧ ¬((ρ a).deg = 0 ∧ d = 0) then
          fieldRes h ρ (montHead p) (.cons (ρ a).var (.cons (ρ a).var .nil))
            ((ρ a).deg + (ρ a).deg - 1) d kk
        else if linB m = true ∨ (ρ a).deg = 0 then
          fieldRes h ρ f (.cons (ρ a).var .nil) (ρ a).deg d kk
        else none
      else opaqueArm f (.cons a .nil) ρ kk
  | none => opaqueArm f (.cons a .nil) ρ kk

/-- **A call**: `binArm` at two word arguments and one word result, `unArm` at one word
    argument and one word result, and `opaqueArm` otherwise. -/
def callArm {Γ Θ : Ctxt jasminDialect} (f : String) {us as rs : List JasminTy}
    (args : HVector (fun t => Var Γ t) as) (ρ : MRen Γ Θ) (d : ℤ) (kk : CallK Γ rs us) :
    Option (NFProg jasminDialect Θ us) :=
  if hs : as = [w64, w64] ∧ rs = [w64] then
    binArm h f (hs.1 ▸ args).head (hs.1 ▸ args).tail.head ρ d (hs.2 ▸ kk)
  else if hs : as = [w64] ∧ rs = [w64] then
    unArm h f (hs.1 ▸ args).head ρ d (hs.2 ▸ kk)
  else opaqueArm f args ρ kk

/-- **The rewriter** from the renaming `ρ` and the degree assignment `H`. A binding is kept on
    arguments read as themselves and continued at its hinted degree (`varConv`); a call is
    rewritten by `callArm`, and a call of a reduce-multiply head is refused; loops and
    branches are kept, with their conditions, counts and carried values read as
    themselves; a returned variable is read as itself. -/
def montifyAux : {Γ : Ctxt jasminDialect} → {ts : List JasminTy} →
    NFProg jasminDialect Γ ts → DegHint → {Θ : Ctxt jasminDialect} → MRen Γ Θ →
      Option (NFProg jasminDialect Θ ts)
  | _, _, .ret vs, _, _, ρ => (sameVars ρ vs).map .ret
  | _, _, .var e k, H, _, ρ => (renExpr ρ e).bind fun e' =>
      (varConv h H.deg (fun g r => montifyAux k H.next (MRen.lift ρ (fun w => g (.there w)) r))).map
        (.var e')
  | _, _, .forLoop (cs := cs) count inits body k, H, _, ρ =>
      (ρ count).same?.bind fun c => (sameVars ρ inits).bind fun ivs =>
        (montifyAux body H.sub1 (MRen.app (MRen.lift ρ (fun w => .there w) (.same .here)) cs)).bind
          fun b' => (montifyAux k H.next (MRen.app ρ cs)).map fun k' => .forLoop c ivs b' k'
  | _, _, .ifThenElse (rs := rs) cond thn els k, H, _, ρ =>
      (ρ cond).same?.bind fun c =>
        (montifyAux thn H.sub1 ρ).bind fun t' => (montifyAux els H.sub2 ρ).bind fun e' =>
          (montifyAux k H.next (MRen.app ρ rs)).map fun k' => .ifThenElse c t' e' k'
  | _, _, .whileLoop (cs := cs) inits body k, H, _, ρ =>
      (sameVars ρ inits).bind fun ivs =>
        (montifyAux body H.sub1 (MRen.app ρ cs)).bind fun b' =>
          (montifyAux k H.next (MRen.app ρ cs)).map fun k' => .whileLoop ivs b' k'
  | _, _, .call f args k, H, _, ρ =>
      if (montTag? f).isSome then none
      else callArm h f args ρ H.deg (fun ρ' => montifyAux k H.next ρ')

/-- **The entry conversions** of the word variables `vs` at their degrees: each variable, read
    as itself, is converted from degree `0` to its degree `d` by `R^(d + 1)` and read at `d`
    from then on, the other readings are kept; then the continuation `kk`. A variable not
    read as itself is refused. -/
def entryConv {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us)) :
    List (Var Γ w64 × ℤ) → {Θ : Ctxt jasminDialect} → MRen Γ Θ →
      Option (NFProg jasminDialect Θ us)
  | [], _, ρ => kk ρ
  | (v, d) :: vs, _, ρ => (ρ v).same?.bind fun x =>
      (entryConv kk vs (MRen.set (ρ.comp fun y => .there (.there y)) v (.mont .here d))).map
        (convProg h x (d + 1))

/-- **The rewriter at the parameter degrees `pd`**, when `montTag?` reads the head
    `montHead p` at `p`: the entry conversions of the word parameters at a nonzero degree of
    `pd` (`paramDegs`), then `montifyAux` from the renaming they give. -/
def montify (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) : Option (NFProg jasminDialect Γ ts) :=
  if montTag? (montHead p) = some p then
    entryConv h (fun ρ => montifyAux h prog H ρ) (paramDegs Γ pd) (idRen Γ)
  else none

/-- **The certificate of a degree assignment**: the rewriter accepts it. -/
def montifyCert (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (prog : NFProg jasminDialect Γ ts) : Bool :=
  (montify h pd H prog).isSome

/-- A program the entry conversions return comes from a program the continuation returns. -/
theorem entryConv_some {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us)) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us), entryConv h kk vs ρ = some q →
      ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen Γ Θ') (q' : NFProg jasminDialect Θ' us),
        kk ρ' = some q'
  | [], _, ρ, q, hq => ⟨_, ρ, q, hq⟩
  | (v, d) :: vs, _, ρ, q, hq => by
      obtain ⟨x, -, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, -⟩ := Option.map_eq_some_iff.mp hq
      exact entryConv_some kk vs _ q1 hq1

/-- At the identity renaming and the empty list the entry conversions are the
    continuation. -/
theorem entryConv_nil {Γ Θ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (ρ : MRen Γ Θ) : entryConv h kk [] ρ = kk ρ := rfl

end Rewrite

/-! ## 6. Soundness -/

section DenoteAt

variable (E : CallEnv jasminDialect) (fuel : Nat)

theorem denoteAt_ret {Γ : Ctxt jasminDialect} {ts : List JasminTy}
    (vs : HVector (fun t => Var Γ t) ts) (V : Valuation Γ) :
    (NFProg.ret (d := jasminDialect) vs).denoteAt E fuel V = some (Expr.lookupArgs vs V) := rfl

theorem denoteAt_var {Γ : Ctxt jasminDialect} {t : JasminTy} {ts : List JasminTy}
    (e : Expr jasminDialect Γ t) (k : NFProg jasminDialect (t :: Γ) ts) (V : Valuation Γ) :
    (NFProg.var e k).denoteAt E fuel V =
      e.denoteM (M := Option) V >>= fun x => k.denoteAt E fuel (V.extend x) := rfl

theorem denoteAt_call {Γ : Ctxt jasminDialect} {as rs ts : List JasminTy} (f : String)
    (args : HVector (fun t => Var Γ t) as) (k : NFProg jasminDialect (rs ++ Γ) ts)
    (V : Valuation Γ) :
    (NFProg.call f args k).denoteAt E fuel V =
      E.call f as rs (Expr.lookupArgs args V) >>= fun r => k.denoteAt E fuel (hvAppend r V) :=
  rfl

theorem denoteAt_forLoop {Γ : Ctxt jasminDialect} {cs ts : List JasminTy}
    (count : Var Γ w64) (inits : HVector (fun t => Var Γ t) cs)
    (body : NFProg jasminDialect (cs ++ w64 :: Γ) cs) (k : NFProg jasminDialect (cs ++ Γ) ts)
    (V : Valuation Γ) :
    (NFProg.forLoop count inits body k).denoteAt E fuel V =
      (List.range (BitVec.toNat (count.lookup V))).foldlM
          (fun acc i => body.denoteAt E fuel
            (hvAppend acc (.cons (t := w64) (BitVec.ofNat 64 i) V)))
          (Expr.lookupArgs inits V) >>= fun acc => k.denoteAt E fuel (hvAppend acc V) := rfl

theorem denoteAt_ifThenElse {Γ : Ctxt jasminDialect} {rs ts : List JasminTy}
    (cond : Var Γ (HasBitType.bit (d := jasminDialect))) (thn els : NFProg jasminDialect Γ rs)
    (k : NFProg jasminDialect (rs ++ Γ) ts) (V : Valuation Γ) :
    (NFProg.ifThenElse cond thn els k).denoteAt E fuel V =
      (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup V) then thn.denoteAt E fuel V
        else els.denoteAt E fuel V) >>= fun r => k.denoteAt E fuel (hvAppend r V) := rfl

end DenoteAt

section Sound

open CatCrypt.Crypto.SecureCompilation.Dialects.NFLeak (forIterLeak whileIterLeak)

variable {p : Nat} (h : mont32Cert p = true) (hm : montTag? (montHead p) = some p)
  (M : LeakModel jasminDialect) (hK : ∀ w n, M.kind (.regConst w n) = .quiet)
  (E : CallEnv jasminDialect) (fuel : Nat)

/-- The leakage run of a `call` node: the callee of the environment, then the continuation at
    the results, with no event of the call. -/
theorem leakRunMC_call (E0 : CallEnv jasminDialect) {Γ : Ctxt jasminDialect}
    {as rs ts : List JasminTy} (f : String) (args : HVector (fun t => Var Γ t) as)
    (k : NFProg jasminDialect (rs ++ Γ) ts) (V : Valuation Γ) :
    Dialects.NFLeak.NFProg.leakRunMC M E0 fuel (NFProg.call f args k) V =
      E0.call f as rs (Expr.lookupArgs args V) >>= fun r =>
        Dialects.NFLeak.NFProg.leakRunMC M E0 fuel k (hvAppend r V) :=
  rfl

include hm hK in
/-- A conversion emits no event: it runs the reduce-multiply of `x` and the constant, then the
    continuation. -/
theorem convProg_leak (E0 : CallEnv jasminDialect) {Θ : Ctxt jasminDialect}
    (x : Var Θ w64) (j : ℤ) {us : List JasminTy}
    (k : NFProg jasminDialect (w64 :: w64 :: Θ) us) (W : Valuation Θ) :
    Dialects.NFLeak.NFProg.leakRunMC M (montEnv E0) fuel (convProg h x j k) W =
      Dialects.NFLeak.NFProg.leakRunMC M (montEnv E0) fuel k (.cons (redcMulW p (x.lookup W)
        (BitVec.ofNat 64 (convC h j))) (.cons (BitVec.ofNat 64 (convC h j)) W)) := by
  have hc : ComLevelCheck.Expr.ctLeak M (eConst (Γ := Θ) (convC h j)) W = [] := by
    simp only [ComLevelCheck.Expr.ctLeak, opLeak, eConst, hK]
  unfold convProg
  simp only [Dialects.NFLeak.NFProg.leakRunMC, Expr.denoteM_option_eq_some, Option.bind_some,
    hc, List.nil_append]
  erw [montEnv_montHead E0 hm]
  simp only [Option.bind_some]
  simp only [Prod.mk.eta, Option.map_id']
  rfl

/-- The conclusion of the soundness of a binding: an extension of the rewritten valuation
    that keeps every lookup, a reading of the bound value related to it, and a program of the
    continuation whose leakage run is that of the rewritten program. -/
def BindOk (E0 : CallEnv jasminDialect) {Θ : Ctxt jasminDialect} {t : JasminTy}
    {us : List JasminTy} (W : Valuation Θ) (x : ⟦t⟧) (kk : BindK Θ t us)
    (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (g : Ctxt.Hom Θ Θ') (r : Rd Θ' t) (W' : Valuation Θ')
    (q' : NFProg jasminDialect Θ' us), Pres g W W' ∧ r.rel h W' x ∧ kk g r = some q' ∧
      Dialects.NFLeak.NFProg.leakRunMC M (montEnv E0) fuel q W =
        Dialects.NFLeak.NFProg.leakRunMC M (montEnv E0) fuel q' W'

include hm hK in
/-- **The result of a field call keeps its value**: a word holding `z` at the degree `k`,
    continued at the degree `d`, is read in relation to the canonical representative of
    `z`. -/
theorem resConv_sound (E0 : CallEnv jasminDialect) {Θ : Ctxt jasminDialect}
    {us : List JasminTy} (v : Var Θ w64) (k d : ℤ) (kk : BindK Θ w64 us)
    (q : NFProg jasminDialect Θ us) (hq : resConv h v k d kk = some q) (W : Valuation Θ)
    (z : ZMod p) (hv : v.lookup W = encK h k z) :
    BindOk h M fuel E0 W (canonEnc p z) kk q := by
  unfold resConv at hq
  split at hq
  · exact ⟨_, fun w => w, rdOf v k, W, q, fun _ => rfl, rdOf_rel h v k z hv, hq, rfl⟩
  · obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
    refine ⟨_, fun w => .there (.there w), rdOf .here d,
      .cons (redcMulW p (v.lookup W) (BitVec.ofNat 64 (convC h (d - k + 1))))
        (.cons (BitVec.ofNat 64 (convC h (d - k + 1))) W), q', fun _ => rfl, ?_, hq',
      convProg_leak h hm M hK fuel E0 v _ q' W⟩
    apply rdOf_rel
    change redcMulW p (v.lookup W) _ = encK h d z
    rw [hv, redcMulW_conv]
    congr 1
    ring

include hm hK in
/-- **A binding keeps its value**: the bound value, continued at the degree `d`, is read in
    relation to itself. -/
theorem varConv_sound (E0 : CallEnv jasminDialect) {Θ : Ctxt jasminDialect}
    {us : List JasminTy} {t : JasminTy} (d : ℤ) (kk : BindK (t :: Θ) t us)
    (q : NFProg jasminDialect (t :: Θ) us) (hq : varConv h d kk = some q)
    (W : Valuation (t :: Θ)) :
    BindOk h M fuel E0 W (Var.here.lookup W) kk q := by
  unfold varConv at hq
  split at hq
  · exact ⟨_, fun w => w, .same .here, W, q, fun _ => rfl, rfl, hq, rfl⟩
  · cases t with
    | reg w =>
      by_cases hw : w = 64
      · subst hw
        obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp hq
        refine ⟨_, fun w => .there (.there w), .mont .here d,
          .cons (redcMulW p (Var.here.lookup W) (BitVec.ofNat 64 (convC h (d + 1))))
            (.cons (BitVec.ofNat 64 (convC h (d + 1))) W), q', fun _ => rfl, ?_, hq',
          convProg_leak h hm M hK fuel E0 .here _ q' W⟩
        intro hx
        have e := redcMulW_conv h 0 (d + 1)
          (((Var.here.lookup W : BitVec 64).toNat : Nat) : ZMod p)
        rw [← word_eq_encK_zero h _ hx, show (0 : ℤ) + (d + 1) - 1 = d by ring] at e
        exact e
      · simp [wordConv, hw] at hq
    | _ => simp [wordConv] at hq

/-- The conclusion of the soundness of a call with the results `r`: a renaming of the source
    context after the call, agreeing with the extended valuations, at which the continuation
    has a rewritten program whose leakage run is that of the rewritten call. -/
def CallOk {Γ Θ : Ctxt jasminDialect} {rs us : List JasminTy} (X : Valuation Γ)
    (W : Valuation Θ) (r : Valuation (d := jasminDialect) rs) (kk : CallK Γ rs us)
    (q : NFProg jasminDialect Θ us) : Prop :=
  ∃ (Θ' : Ctxt jasminDialect) (ρ' : MRen (rs ++ Γ) Θ') (W' : Valuation Θ')
    (q' : NFProg jasminDialect Θ' us), kk ρ' = some q' ∧ MAgree h ρ' (hvAppend r X) W' ∧
      Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q W =
        Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q' W'

theorem opaqueArm_sound {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    {as rs us : List JasminTy} (args : HVector (fun t => Var Γ t) as) {ρ : MRen Γ Θ}
    {X : Valuation Γ} {W : Valuation Θ} (hA : MAgree h ρ X W) (kk : CallK Γ rs us)
    (q : NFProg jasminDialect Θ us) (hq : opaqueArm f args ρ kk = some q)
    (r : Valuation (d := jasminDialect) rs)
    (hr : (fieldEnv E).call f as rs (Expr.lookupArgs args X) = some r) :
    CallOk h M E fuel X W r kk q := by
  obtain ⟨args', hargs, hq⟩ := Option.bind_eq_some_iff.mp hq
  obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
  refine ⟨_, MRen.app ρ rs, hvAppend r W, k', hk', MAgree.app h hA rs r, ?_⟩
  rw [leakRunMC_call, montEnv_of_none _ hf, sameVars_lookup h hA args args' hargs, hr]
  rfl

include hm hK in
theorem fieldRes_sound {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) (g : String) {as us : List JasminTy}
    (args : HVector (fun t => Var Θ t) as) (k d : ℤ) (kk : CallK Γ [w64] us)
    (q : NFProg jasminDialect Θ us) (hq : fieldRes h ρ g args k d kk = some q) (z : ZMod p)
    (hg : (montEnv (fieldEnv E)).call g as [w64] (Expr.lookupArgs args W) =
      some (.cons (encK h k z) .nil)) :
    CallOk h M E fuel X W (.cons (canonEnc p z) .nil) kk q := by
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  obtain ⟨Θ', g', r, W', q', hp, hr, hk, hden⟩ :=
    resConv_sound h hm M hK fuel (fieldEnv E) .here k d (resK ρ kk) q0 hq0
      (.cons (encK h k z) W) z rfl
  refine ⟨Θ', MRen.lift ρ (fun w => g' (.there w)) r, W', q', hk,
    hA.lift h (g := fun w => g' (.there w)) (fun v => hp (.there v)) r _ hr, ?_⟩
  rw [leakRunMC_call, hg]
  exact hden

/-- The value of a method on numbers below `p` is the operation of `ZMod p`. -/
theorem fieldVal_nat [NeZero p] (m : FieldMethod) {a b : Nat} (ha : a < p) (hb : b < p) :
    ((fieldVal m p a b : Nat) : ZMod p) = fieldOp m (a : ZMod p) (b : ZMod p) := by
  have e := fieldVal_cast m (a : ZMod p) (b : ZMod p)
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at e

include h in
/-- **A source call of a method with two arguments at `p`**: its arguments are below `p` and
    its result is the canonical representative of the operation. -/
theorem fieldCall_bin {f : String} {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hbin : m.binary = true) (xa xb : BitVec 64) (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv E).call f [w64, w64] [w64] (.cons xa (.cons xb .nil)) = some r) :
    xa.toNat < p ∧ xb.toNat < p ∧
      r = .cons (canonEnc p (fieldOp m (xa.toNat : ZMod p) (xb.toNat : ZMod p))) .nil := by
  have := neZero_of_cert h
  have h64 := lt_two64_of_cert h
  rw [fieldEnv_of_isSome E (by simp [ht])] at hr
  cases m <;> simp only [FieldMethod.binary, Bool.false_eq_true] at hbin <;>
  · obtain ⟨ha, hb, rfl⟩ := tableEnv_field h64 ht (.cons xa (.cons xb .nil)) r hr
    have ha' : xa.toNat < p := ha
    have hb' : xb.toNat < p := hb rfl
    refine ⟨ha', hb', ?_⟩
    simp only [fieldNats]
    rw [fieldVal_nat _ ha' hb']

include h in
/-- **A source call of a method with one argument at `p`**: its argument is below `p` and its
    result is the canonical representative of the operation. -/
theorem fieldCall_un {f : String} {m : FieldMethod} (ht : fieldTag? f = some (m, p))
    (hun : m.binary = false) (xa : BitVec 64) (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv E).call f [w64] [w64] (.cons xa .nil) = some r) :
    xa.toNat < p ∧ r = .cons (canonEnc p (fieldOp m (xa.toNat : ZMod p) 0)) .nil := by
  have := neZero_of_cert h
  have h64 := lt_two64_of_cert h
  rw [fieldEnv_of_isSome E (by simp [ht])] at hr
  cases m <;> simp only [FieldMethod.binary, Bool.true_eq_false] at hun <;>
  · obtain ⟨ha, -, rfl⟩ := tableEnv_field h64 ht (.cons xa .nil) r hr
    have ha' : xa.toNat < p := ha
    refine ⟨ha', ?_⟩
    simp only [fieldNats]
    rw [fieldVal_nat _ ha' (Nat.pos_of_neZero p), Nat.cast_zero]

/-- **A kept call of a method with two arguments** on operands at the degree `k` returns the
    value at the degree `k`, for a method that commutes with constants or at degree `0`. -/
theorem keepCall_bin {f : String} (hf : montTag? f = none) {m : FieldMethod}
    (ht : fieldTag? f = some (m, p)) (hbin : m.binary = true) (k : ℤ)
    (hk : linB m = true ∨ k = 0) (A B : ZMod p) :
    (montEnv (fieldEnv E)).call f [w64, w64] [w64] (.cons (encK h k A) (.cons (encK h k B) .nil))
      = some (.cons (encK h k (fieldOp m A B)) .nil) := by
  have := neZero_of_cert h
  have h64 := lt_two64_of_cert h
  rw [montEnv_of_none _ hf, fieldEnv_of_isSome E (by simp [ht])]
  have hc : linB m = true ∨ ((R32 h ^ k : (ZMod p)ˣ) : ZMod p) = 1 :=
    hk.imp id fun h0 => by subst h0; simp
  have key : canonEnc p ((fieldVal m p (encK h k A).toNat (encK h k B).toNat : Nat) : ZMod p)
      = encK h k (fieldOp m A B) := by
    rw [encK_toNat, encK_toNat, fieldVal_cast, fieldOp_mul_right m A B _ hc]
    rfl
  cases m <;> simp only [FieldMethod.binary, Bool.false_eq_true] at hbin <;>
  · refine (tableEnv_field_some h64 ht (.cons (encK h k A) (.cons (encK h k B) .nil))
      (encK_toNat_lt h k A) (fun _ => encK_toNat_lt h k B)).trans ?_
    simp only [fieldNats]
    rw [key]

/-- **A kept call of a method with one argument** on an operand at the degree `k` returns the
    value at the degree `k`, for a method that commutes with constants or at degree `0`. -/
theorem keepCall_un {f : String} (hf : montTag? f = none) {m : FieldMethod}
    (ht : fieldTag? f = some (m, p)) (hun : m.binary = false) (k : ℤ)
    (hk : linB m = true ∨ k = 0) (A : ZMod p) :
    (montEnv (fieldEnv E)).call f [w64] [w64] (.cons (encK h k A) .nil)
      = some (.cons (encK h k (fieldOp m A 0)) .nil) := by
  have := neZero_of_cert h
  have h64 := lt_two64_of_cert h
  rw [montEnv_of_none _ hf, fieldEnv_of_isSome E (by simp [ht])]
  have hc : linB m = true ∨ ((R32 h ^ k : (ZMod p)ˣ) : ZMod p) = 1 :=
    hk.imp id fun h0 => by subst h0; simp
  have e0 : ((0 : ZMod p) * ((R32 h ^ k : (ZMod p)ˣ) : ZMod p)).val = 0 := by simp
  have key : canonEnc p ((fieldVal m p (encK h k A).toNat 0 : Nat) : ZMod p)
      = encK h k (fieldOp m A 0) := by
    rw [encK_toNat, ← e0, fieldVal_cast, fieldOp_mul_right m A 0 _ hc]
    rfl
  cases m <;> simp only [FieldMethod.binary, Bool.true_eq_false] at hun <;>
  · refine (tableEnv_field_some h64 ht (.cons (encK h k A) .nil) (encK_toNat_lt h k A)
      (fun hb => by simp [FieldMethod.binary] at hb)).trans ?_
    simp only [fieldNats]
    rw [key]

include hm in
/-- **The reduce-multiply call** on operands at the degrees `k` and `j` returns the product
    at the degree `k + j − 1`. -/
theorem redcCall (E0 : CallEnv jasminDialect) (k j : ℤ) (A B : ZMod p) :
    (montEnv E0).call (montHead p) [w64, w64] [w64]
      (.cons (encK h k A) (.cons (encK h j B) .nil)) =
      some (.cons (encK h (k + j - 1) (A * B)) .nil) := by
  rw [montEnv_montHead E0 hm, redcMulW_encK]

include hm hK in
/-- **A call with two word arguments keeps its result.** -/
theorem binArm_sound {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (a b : Var Γ w64) {ρ : MRen Γ Θ} {X : Valuation Γ} {W : Valuation Θ}
    (hA : MAgree h ρ X W) (d : ℤ) {us : List JasminTy} (kk : CallK Γ [w64] us)
    (q : NFProg jasminDialect Θ us) (hq : binArm h f a b ρ d kk = some q)
    (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv E).call f [w64, w64] [w64] (.cons (a.lookup X) (.cons (b.lookup X) .nil))
      = some r) :
    CallOk h M E fuel X W r kk q := by
  unfold binArm at hq
  split at hq
  · rename_i m q' ht
    split at hq
    · rename_i hc
      obtain ⟨rfl, hbin⟩ := hc
      obtain ⟨ha, hb, rfl⟩ := fieldCall_bin h E ht hbin _ _ r hr
      have hva := Rd.rel_canon h (ρ a) _ (hA _ a) ha
      have hvb := Rd.rel_canon h (ρ b) _ (hA _ b) hb
      split at hq
      · rename_i hmul
        obtain ⟨rfl, -⟩ := hmul
        refine fieldRes_sound h hm M hK E fuel hA _ _ _ _ kk q hq _ ?_
        change (montEnv (fieldEnv E)).call (montHead q') [w64, w64] [w64]
          (.cons ((ρ a).var.lookup W) (.cons ((ρ b).var.lookup W) .nil)) = _
        rw [hva, hvb, redcCall h hm]
        rfl
      · split at hq
        · rename_i hkeep
          obtain ⟨hdeg, hlin⟩ := hkeep
          refine fieldRes_sound h hm M hK E fuel hA _ _ _ _ kk q hq _ ?_
          change (montEnv (fieldEnv E)).call f [w64, w64] [w64]
            (.cons ((ρ a).var.lookup W) (.cons ((ρ b).var.lookup W) .nil)) = _
          rw [hva, hvb, ← hdeg]
          exact keepCall_bin h E hf ht hbin _ hlin _ _
        · cases hq
    · exact opaqueArm_sound h M E fuel hf _ hA kk q hq r hr
  · exact opaqueArm_sound h M E fuel hf _ hA kk q hq r hr

include hm hK in
/-- **A call with one word argument keeps its result.** -/
theorem unArm_sound {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    (a : Var Γ w64) {ρ : MRen Γ Θ} {X : Valuation Γ} {W : Valuation Θ}
    (hA : MAgree h ρ X W) (d : ℤ) {us : List JasminTy} (kk : CallK Γ [w64] us)
    (q : NFProg jasminDialect Θ us) (hq : unArm h f a ρ d kk = some q)
    (r : Valuation (d := jasminDialect) [w64])
    (hr : (fieldEnv E).call f [w64] [w64] (.cons (a.lookup X) .nil) = some r) :
    CallOk h M E fuel X W r kk q := by
  unfold unArm at hq
  split at hq
  · rename_i m q' ht
    split at hq
    · rename_i hc
      obtain ⟨rfl, hun⟩ := hc
      obtain ⟨ha, rfl⟩ := fieldCall_un h E ht hun _ r hr
      have hva := Rd.rel_canon h (ρ a) _ (hA _ a) ha
      split at hq
      · rename_i hsq
        obtain ⟨rfl, -⟩ := hsq
        refine fieldRes_sound h hm M hK E fuel hA _ _ _ _ kk q hq _ ?_
        change (montEnv (fieldEnv E)).call (montHead q') [w64, w64] [w64]
          (.cons ((ρ a).var.lookup W) (.cons ((ρ a).var.lookup W) .nil)) = _
        rw [hva, redcCall h hm]
        rfl
      · split at hq
        · rename_i hlin
          refine fieldRes_sound h hm M hK E fuel hA _ _ _ _ kk q hq _ ?_
          change (montEnv (fieldEnv E)).call f [w64] [w64]
            (.cons ((ρ a).var.lookup W) .nil) = _
          rw [hva]
          exact keepCall_un h E hf ht hun _ hlin _
        · cases hq
    · exact opaqueArm_sound h M E fuel hf _ hA kk q hq r hr
  · exact opaqueArm_sound h M E fuel hf _ hA kk q hq r hr

include hm hK in
/-- **A call keeps its results**: the rewriter of a call returns a program whose leakage run
    is that of the rewritten continuation at a renaming that agrees with the results of the
    source call. -/
theorem callArm_sound {Γ Θ : Ctxt jasminDialect} {f : String} (hf : montTag? f = none)
    {us as rs : List JasminTy} (args : HVector (fun t => Var Γ t) as) {ρ : MRen Γ Θ}
    {X : Valuation Γ} {W : Valuation Θ} (hA : MAgree h ρ X W) (d : ℤ) (kk : CallK Γ rs us)
    (q : NFProg jasminDialect Θ us) (hq : callArm h f args ρ d kk = some q)
    (r : Valuation (d := jasminDialect) rs)
    (hr : (fieldEnv E).call f as rs (Expr.lookupArgs args X) = some r) :
    CallOk h M E fuel X W r kk q := by
  unfold callArm at hq
  split at hq
  · rename_i hs
    obtain ⟨rfl, rfl⟩ := hs
    rcases args with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    exact binArm_sound h hm M hK E fuel hf a b hA _ kk q hq r hr
  · split at hq
    · rename_i hs
      obtain ⟨rfl, rfl⟩ := hs
      rcases args with _ | ⟨a, _ | _⟩
      exact unArm_sound h hm M hK E fuel hf a hA _ kk q hq r hr
    · exact opaqueArm_sound h M E fuel hf _ hA kk q hq r hr

/-- The events of a rewritten expression are the events of the source expression. -/
theorem renExpr_ctLeak {Γ Θ : Ctxt jasminDialect} {ρ : MRen Γ Θ} {X : Valuation Γ}
    {W : Valuation Θ} (hA : MAgree h ρ X W) {t : JasminTy} (e : Expr jasminDialect Γ t)
    (e' : Expr jasminDialect Θ t) (he : renExpr ρ e = some e') :
    ComLevelCheck.Expr.ctLeak M e' W = ComLevelCheck.Expr.ctLeak M e X := by
  obtain ⟨op, rfl, args⟩ := e
  obtain ⟨args', ha, rfl⟩ := Option.map_eq_some_iff.mp he
  show opLeak M op (Expr.lookupArgs args' W) = opLeak M op (Expr.lookupArgs args X)
  rw [sameVars_lookup h hA args args' ha]

include hm hK in
/-- **The rewriter keeps the results and the events.** For a program `prog` rewritten from
    the renaming `ρ` and valuations `X`, `W` that agree along `ρ`: a leakage run of `prog` at
    `fieldEnv E` to the results and events `R` is matched, at the same fuel, by a leakage run
    of the rewritten program at `montEnv (fieldEnv E)` to `R`, at a leakage model whose
    register constants are quiet. -/
theorem montifyAux_leakSound :
    ∀ {Γ : Ctxt jasminDialect} {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
      (H : DegHint) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ) (q : NFProg jasminDialect Θ ts),
      montifyAux h prog H ρ = some q → ∀ (X : Valuation Γ) (W : Valuation Θ),
        MAgree h ρ X W → ∀ R,
          Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel prog X = some R →
          Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q W = some R
  | _, _, .ret vs, _, _, ρ, q, hq, X, W, hA, R, hR => by
      obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hq
      change some (Expr.lookupArgs vs X, []) = some R at hR
      change some (Expr.lookupArgs ws W, []) = some R
      rw [sameVars_lookup h hA vs ws hws]
      exact hR
  | _, _, .var e k, H, _, ρ, q, hq, X, W, hA, R, hR => by
      obtain ⟨e', he, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [Dialects.NFLeak.NFProg.leakRunMC] at hR ⊢
      obtain ⟨x, hx, hR⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨R0, hR0, rfl⟩ := Option.map_eq_some_iff.mp hR
      obtain ⟨Θ', g, r, W', q', hp, hr, hk, hden⟩ :=
        varConv_sound h hm M hK fuel (fieldEnv E) H.deg _ q0 hq0 (W.extend x)
      rw [renExpr_denoteM h hA e e' he, hx, Option.bind_some, renExpr_ctLeak h M hA e e' he,
        hden, montifyAux_leakSound k H.next _ q' hk (X.extend x) W'
          (hA.lift h (g := fun w => g (.there w)) (fun v => hp (.there v)) r x hr) R0 hR0,
        Option.map_some]
  | _, _, .forLoop (cs := cs) count inits body k, H, _, ρ, q, hq, X, W, hA, R, hR => by
      obtain ⟨c, hc, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨ivs, hivs, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      have hcnt : c.lookup W = count.lookup X := by
        have h0 : (ρ count).rel h W (count.lookup X) := hA _ count
        have e : ρ count = .same c := Rd.eq_of_same? hc
        rw [e] at h0
        exact h0
      simp only [Dialects.NFLeak.NFProg.leakRunMC] at hR ⊢
      obtain ⟨acc, hfold, hkout⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨R0, hR0, rfl⟩ := Option.map_eq_some_iff.mp hkout
      have hfold' : ∀ (l : List Nat) (a : Valuation (d := jasminDialect) cs) b,
          forIterLeak (fun i acc => Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel body
            (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) X))) l a = some b →
          forIterLeak (fun i acc => Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E))
            fuel b' (hvAppend acc (.cons (HasWord64.ofNat (d := jasminDialect) i) W))) l a =
            some b := by
        intro l
        induction l with
        | nil => exact fun _ _ hab => hab
        | cons i l ih =>
          intro a b hab
          simp only [forIterLeak] at hab ⊢
          obtain ⟨a1, ha1, hab⟩ := Option.bind_eq_some_iff.mp hab
          obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hab
          have hag : MAgree h (MRen.app (MRen.lift ρ (fun w => .there w)
              (.same (Θ := HasWord64.word (d := jasminDialect) :: _) .here)) cs)
              (hvAppend a (.cons (HasWord64.ofNat (d := jasminDialect) i) X))
              (hvAppend a (.cons (HasWord64.ofNat (d := jasminDialect) i) W)) :=
            MAgree.app h (hA.lift h (g := fun w => .there w)
              (W' := HVector.cons (HasWord64.ofNat (d := jasminDialect) i) W) (fun _ => rfl)
              (.same .here) (HasWord64.ofNat (d := jasminDialect) i) rfl) cs a
          rw [montifyAux_leakSound body H.sub1 _ b' hb' _ _ hag a1 ha1, Option.bind_some,
            ih a1.1 b1 hb1, Option.map_some]
      rw [hcnt, sameVars_lookup h hA inits ivs hivs, hfold' _ _ _ hfold, Option.bind_some,
        montifyAux_leakSound k H.next _ k' hk' _ _ (MAgree.app h hA cs acc.1) R0 hR0,
        Option.map_some]
  | _, _, .ifThenElse (rs := rs) cond thn els k, H, _, ρ, q, hq, X, W, hA, R, hR => by
      obtain ⟨c, hc, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨t', ht', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨e', he', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      have hcond : c.lookup W = cond.lookup X := by
        have h0 : (ρ cond).rel h W (cond.lookup X) := hA _ cond
        have e : ρ cond = .same c := Rd.eq_of_same? hc
        rw [e] at h0
        exact h0
      simp only [Dialects.NFLeak.NFProg.leakRunMC] at hR ⊢
      obtain ⟨r0, hr0, hkout⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨R0, hR0, rfl⟩ := Option.map_eq_some_iff.mp hkout
      have hr0' : (if HasBoolBit.toBool (d := jasminDialect) (cond.lookup X) then
          Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel t' W
          else Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel e' W) =
            some r0 := by
        by_cases hb : HasBoolBit.toBool (d := jasminDialect) (cond.lookup X) = true
        · rw [ite_eq_left hb] at hr0 ⊢
          exact montifyAux_leakSound thn H.sub1 ρ t' ht' X W hA r0 hr0
        · rw [ite_eq_right hb] at hr0 ⊢
          exact montifyAux_leakSound els H.sub2 ρ e' he' X W hA r0 hr0
      rw [hcond, hr0', Option.bind_some,
        montifyAux_leakSound k H.next _ k' hk' _ _ (MAgree.app h hA rs r0.1) R0 hR0,
        Option.map_some]
  | _, _, .whileLoop (cs := cs) inits body k, H, _, ρ, q, hq, X, W, hA, R, hR => by
      obtain ⟨ivs, hivs, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨b', hb', hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.mp hq
      simp only [Dialects.NFLeak.NFProg.leakRunMC] at hR ⊢
      obtain ⟨acc, hiter, hkout⟩ := Option.bind_eq_some_iff.mp hR
      obtain ⟨R0, hR0, rfl⟩ := Option.map_eq_some_iff.mp hkout
      have hw : ∀ (n : Nat) (a : Valuation (d := jasminDialect) cs) b,
          whileIterLeak (fun acc => Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel body
            (hvAppend acc X)) n a = some b →
          whileIterLeak (fun acc => Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E))
            fuel b' (hvAppend acc W)) n a = some b := by
        intro n
        induction n with
        | zero => exact fun _ _ hab => by cases hab
        | succ n ih =>
          intro a b hab
          simp only [whileIterLeak] at hab ⊢
          obtain ⟨r1, hr1, hab⟩ := Option.bind_eq_some_iff.mp hab
          rw [montifyAux_leakSound body H.sub1 _ b' hb' _ _ (MAgree.app h hA cs a) r1 hr1,
            Option.bind_some]
          by_cases hc : HasBoolBit.toBool (d := jasminDialect) r1.1.head = true
          · rw [ite_eq_left hc] at hab ⊢
            obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp hab
            rw [ih _ _ hb1, Option.map_some]
          · rw [ite_eq_right hc] at hab ⊢
            exact hab
      rw [sameVars_lookup h hA inits ivs hivs, hw _ _ _ hiter, Option.bind_some,
        montifyAux_leakSound k H.next _ k' hk' _ _ (MAgree.app h hA cs acc.1) R0 hR0,
        Option.map_some]
  | _, _, .call f args k, H, _, ρ, q, hq, X, W, hA, R, hR => by
      unfold montifyAux at hq
      split at hq
      · cases hq
      · rename_i hf
        have hf' : montTag? f = none := Option.not_isSome_iff_eq_none.mp hf
        rw [leakRunMC_call] at hR
        obtain ⟨r, hr, hkout⟩ := Option.bind_eq_some_iff.mp hR
        obtain ⟨Θ', ρ', W', q', hk, hA', hden⟩ :=
          callArm_sound h hm M hK E fuel hf' args hA _ _ q hq r hr
        rw [hden]
        exact montifyAux_leakSound k H.next ρ' q' hk _ W' hA' R hkout

include hm hK in
/-- **The entry conversions keep the results and the events.** When `entryConv` returns `q`
    from a renaming that agrees with `X` and `W`, and every program the continuation returns
    from a renaming that agrees with `X` and a valuation `W'` has the leakage run `S` at `W'`,
    the leakage run of `q` at `W` is `S`. -/
theorem entryConv_leakSound {Γ : Ctxt jasminDialect} {us : List JasminTy}
    (kk : ∀ {Θ : Ctxt jasminDialect}, MRen Γ Θ → Option (NFProg jasminDialect Θ us))
    (X : Valuation Γ) (S : Option (Valuation (d := jasminDialect) us × List CTLeak))
    (hk : ∀ {Θ' : Ctxt jasminDialect} (ρ' : MRen Γ Θ') (q' : NFProg jasminDialect Θ' us)
      (W' : Valuation Θ'), kk ρ' = some q' → MAgree h ρ' X W' →
        Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q' W' = S) :
    ∀ (vs : List (Var Γ w64 × ℤ)) {Θ : Ctxt jasminDialect} (ρ : MRen Γ Θ)
      (q : NFProg jasminDialect Θ us) (W : Valuation Θ), entryConv h kk vs ρ = some q →
      MAgree h ρ X W → Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q W = S
  | [], _, ρ, q, W, hq, hA => hk ρ q W hq hA
  | (v, d) :: vs, _, ρ, q, W, hq, hA => by
      obtain ⟨x, hx, hq⟩ := Option.bind_eq_some_iff.mp hq
      obtain ⟨q1, hq1, rfl⟩ := Option.map_eq_some_iff.mp hq
      have hxv : x.lookup W = v.lookup X := by
        have h0 : (ρ v).rel h W (v.lookup X) := hA _ v
        have e : ρ v = .same x := Rd.eq_of_same? hx
        rw [e] at h0
        exact h0
      rw [convProg_leak h hm M hK fuel (fieldEnv E) x (d + 1) q1 W]
      refine entryConv_leakSound kk X S hk vs _ q1 _ hq1 ?_
      refine MAgree.set h (MAgree.comp h hA (g := fun y => .there (.there y))
        (W' := .cons (t := w64) (redcMulW p (x.lookup W) (BitVec.ofNat 64 (convC h (d + 1))))
          (.cons (t := w64) (BitVec.ofNat 64 (convC h (d + 1))) W)) ?_) v _ ?_
      · intro _ _
        rfl
      intro hlt
      have e := redcMulW_conv h 0 (d + 1) (((v.lookup X : BitVec 64).toNat : Nat) : ZMod p)
      rw [← word_eq_encK_zero h _ hlt, show (0 : ℤ) + (d + 1) - 1 = d by ring] at e
      change redcMulW p (x.lookup W) (BitVec.ofNat 64 (convC h (d + 1))) = _
      rw [hxv]
      exact e

include hK in
/-- **Soundness of the rewriter for the leakage run.** When `montify` accepts the parameter
    degrees `pd` and the degree assignment `H` and returns `q`, a leakage run of `prog` at
    `fieldEnv E` is matched, at the same fuel, by a leakage run of `q` at
    `montEnv (fieldEnv E)` to the same results and events, at a leakage model whose register
    constants are quiet. -/
theorem montify_leakSound (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (q : NFProg jasminDialect Γ ts)
    (hq : montify h pd H prog = some q) (X : Valuation Γ)
    (R : Valuation (d := jasminDialect) ts × List CTLeak)
    (hR : Dialects.NFLeak.NFProg.leakRunMC M (fieldEnv E) fuel prog X = some R) :
    Dialects.NFLeak.NFProg.leakRunMC M (montEnv (fieldEnv E)) fuel q X = some R := by
  unfold montify at hq
  split at hq
  · rename_i hm'
    exact entryConv_leakSound h hm' M hK E fuel (fun ρ => montifyAux h prog H ρ) X (some R)
      (fun ρ' q' W' hk hA' => montifyAux_leakSound h hm' M hK E fuel prog H ρ' q' hk X W' hA' R hR)
      (paramDegs Γ pd) (idRen Γ) q X hq (idRen_agree h X)
  · cases hq

end Sound

/-- The leakage model in which every operation is quiet. -/
def quietModel : LeakModel jasminDialect where
  kind _ := .quiet
  valNat _ _ := 0

section SoundDen

variable {p : Nat} (h : mont32Cert p = true) (E : CallEnv jasminDialect) (fuel : Nat)

/-- **Soundness of the rewriter.** When `montify` accepts the parameter degrees `pd` and the
    degree assignment `H` and returns `q`, a run of `prog` at `fieldEnv E` to the result `R` is
    matched, at the same fuel, by a run of `q` at `montEnv (fieldEnv E)` to `R`: the returned
    words, which are at degree `0`, are the encodings `encK h 0` of the source values, the
    values themselves. -/
theorem montify_sound (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts) (q : NFProg jasminDialect Γ ts)
    (hq : montify h pd H prog = some q) (X : Valuation Γ)
    (R : Valuation (d := jasminDialect) ts)
    (hR : prog.denoteAt (fieldEnv E) fuel X = some R) :
    q.denoteAt (montEnv (fieldEnv E)) fuel X = some R := by
  rw [← Dialects.NFLeak.NFProg.leakRunMC_fst quietModel] at hR ⊢
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp hR
  rw [montify_leakSound h quietModel (fun _ _ => rfl) E fuel pd H prog q hq X r hr,
    Option.map_some]

/-- **A passing certificate gives a sound rewrite**: `montify` returns a program that, at
    `montEnv (fieldEnv E)`, returns every result the source program returns at
    `fieldEnv E`. -/
theorem montifyCert_sound (pd : List ℤ) (H : DegHint) {Γ : Ctxt jasminDialect}
    {ts : List JasminTy} (prog : NFProg jasminDialect Γ ts)
    (hc : montifyCert h pd H prog = true) :
    ∃ q, montify h pd H prog = some q ∧
      ∀ (X : Valuation Γ) (R : Valuation (d := jasminDialect) ts),
        prog.denoteAt (fieldEnv E) fuel X = some R →
          q.denoteAt (montEnv (fieldEnv E)) fuel X = some R := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hc
  exact ⟨q, hq, fun X R hR => montify_sound h E fuel pd H prog q hq X R hR⟩

end SoundDen

end CatCrypt.Crypto.SecureCompilation.Haxc.NFMontify
