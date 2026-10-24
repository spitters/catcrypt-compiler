/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import HaxLean.AST
public import HaxAscent.RustSemantics.Bitwise
public import HaxAscent.Ascent.Corres

/-!
# The `RustM` reading of the word fragment of haxpipe literals

The word fragment at an unsigned width `ty` is the part of the `ImpExpr` language whose
every value is a `ty`-scalar: integer literals, variables, `let`, the width-tagged
operations `BitAnd#w`, `BitOr#w`, `BitXor#w`, `wrapping_add#w`, `wrapping_sub#w`,
`wrapping_mul#w`, `Shr#w`, `Shl#w`, `rotate_right#w`, `rotate_left#w` and `Not#w` whose
tag `w` is the
tag of `ty` (`uTag`: the width in decimal, `size` for `usize`), and type ascriptions.

* `toRustM ty e ρ` reads `e` as an Aeneas program over `Aeneas.Std.RustM`, each tagged
  name read as the Aeneas operation of its class-1 square (`WordOp.aen`). It fails on a
  construct outside the fragment, on an unbound variable and on a literal outside the
  range of `ty`.
* `runWord ty e ρ` reads `e` over the runtime's unbounded integers, each tagged name read
  as the runtime operation `Hax.*_w ty.numBits` that the haxpipe surface calls
  (`WordOp.rt`).

The names are compared as strings built by `String.append` from the tag, not by printing
the width, so that the kernel decides a comparison in a `module` file, where `Nat.repr` is
not exposed.

## Pasting

`WordOp.square` is the class-1 square of each operation, taken from
`HaxAscent/RustSemantics/Bitwise.lean` (and `wrapping_sub_w_u_square`,
`rotate_left_w_u_square` below). The
pasting theorem `toRustM_square` composes them along the expression: for environments
related by the encoding (`EnvRel`), `RCompOk EncRel (toRustM ty e ρA)
(pure (runWord ty e ρI))`, so every value the Aeneas program returns encodes the runtime
value. `toRustM_isOk_of_totalOk` states that the reading returns a value when the
expression passes the Boolean check `totalOk` (every literal in range, every shift and
rotation amount a literal below the bound of its operation) and every free variable is
bound; on such an expression the square is not vacuous.

## Composition with the ascent

`fnCorres_toRustM` composes the square with a function correspondence `FnCorres bi e entry
G f` of the ascent: when the surface function is the runtime reading of its literal
(`runWord ty e (ρI a) = f a`), every value the Aeneas reading returns is, from some fuel
on, the value `denote'` computes on the literal, up to the two encodings (Aeneas scalar to
`Int`, `Int` to `Hax.Value`).

## Main definitions

* `uTag`, `WordOp`, `WordOp.ofName`, `WordOp.aen`, `WordOp.rt`, `WordOp.square`
* `toRustM`, `runWord`, `EnvRel`, `totalOk`
* `toRustM_square`, `toRustM_isOk_of_totalOk`, `fnCorres_toRustM`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Hax.RustSemantics

open Aeneas.Std

/-- Unsigned `wrapping_sub` agrees with the width-aware runtime `Hax.wrapping_sub_w`. -/
theorem wrapping_sub_w_u_square {ty : UScalarTy} (x y : UScalar ty) :
    RCompOk EncRel (lift (UScalar.wrapping_sub x y))
      (pure (Hax.wrapping_sub_w ty.numBits (enc x) (enc y)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv - y.bv).toNat : Int) = Hax.wrapping_sub_w _ (x.val : Int) (y.val : Int)
  have hx := x.bv.isLt
  have hy := y.bv.isLt
  simp only [Hax.wrapping_sub_w, Hax.mod2w, BitVec.toNat_sub, UScalar.val]
  have : ((x.bv.toNat : Int) - y.bv.toNat + ((2 ^ ty.numBits : Nat) : Int)).toNat
      = 2 ^ ty.numBits - y.bv.toNat + x.bv.toNat := by
    omega
  push_cast at this ⊢
  rw [this]
  simp

/-- The binary operations of the word fragment. -/
inductive WordOp
  | band | bor | bxor | wadd | wsub | wmul | shr | shl | rotr | rotl
  deriving DecidableEq

/-- The width tag of an unsigned type in a runtime operation name `op#tag`. -/
def uTag : UScalarTy → String
  | .Usize => "size"
  | .U8 => "8"
  | .U16 => "16"
  | .U32 => "32"
  | .U64 => "64"
  | .U128 => "128"

/-- The operation a name tagged `tag` denotes. -/
def WordOp.ofName (tag : String) (f : String) : Option WordOp :=
  if f = "BitAnd#" ++ tag then some .band
  else if f = "BitOr#" ++ tag then some .bor
  else if f = "BitXor#" ++ tag then some .bxor
  else if f = "wrapping_add#" ++ tag then some .wadd
  else if f = "wrapping_sub#" ++ tag then some .wsub
  else if f = "wrapping_mul#" ++ tag then some .wmul
  else if f = "Shr#" ++ tag then some .shr
  else if f = "Shl#" ++ tag then some .shl
  else if f = "rotate_right#" ++ tag then some .rotr
  else if f = "rotate_left#" ++ tag then some .rotl
  else none

/-- The Aeneas operation of a word operation. A rotation amount is an Aeneas `U32`; an
    amount of `2 ^ 32` or more fails. -/
def WordOp.aen {ty : UScalarTy} : WordOp → UScalar ty → UScalar ty → RustM (UScalar ty)
  | .band, x, y => lift (x &&& y)
  | .bor, x, y => lift (x ||| y)
  | .bxor, x, y => lift (x ^^^ y)
  | .wadd, x, y => lift (UScalar.wrapping_add x y)
  | .wsub, x, y => lift (UScalar.wrapping_sub x y)
  | .wmul, x, y => lift (UScalar.wrapping_mul x y)
  | .shr, x, y => x >>> y
  | .shl, x, y => x <<< y
  | .rotr, x, y =>
    if h : y.val < 2 ^ UScalarTy.U32.numBits then
      lift (UScalar.rotate_right x (UScalar.ofNatCore (ty := .U32) y.val h))
    else .fail .undef
  | .rotl, x, y =>
    if h : y.val < 2 ^ UScalarTy.U32.numBits then
      lift (UScalar.rotate_left x (UScalar.ofNatCore (ty := .U32) y.val h))
    else .fail .undef

/-- The runtime operation of a word operation at width `w`. -/
def WordOp.rt (w : Nat) : WordOp → Int → Int → Int
  | .band => Hax.bitand_w w
  | .bor => Hax.bitor_w w
  | .bxor => Hax.bitxor_w w
  | .wadd => Hax.wrapping_add_w w
  | .wsub => Hax.wrapping_sub_w w
  | .wmul => Hax.wrapping_mul_w w
  | .shr => Hax.shr_w w
  | .shl => Hax.shl_w w
  | .rotr => Hax.rotate_right_w w
  | .rotl => Hax.rotate_left_w w

/-- Unsigned `rotate_left` agrees with `Hax.rotate_left_w` at the operand width. -/
theorem rotate_left_w_u_square {ty : UScalarTy} (x : UScalar ty) (s : U32) :
    RCompOk EncRel (lift (UScalar.rotate_left x s))
      (pure (Hax.rotate_left_w ty.numBits (enc x) (enc s)) : Id Int) := by
  rw [rcompOk_lift]
  show ((x.bv.rotateLeft s.val).toNat : Int) = Hax.rotate_left_w _ (x.val : Int) (s.val : Int)
  simp only [Hax.rotate_left_w, Hax.mod2w, Int.toNat_natCast, BitVec.toNat_rotateLeft,
    Nat.or_mod_two_pow, UScalar.val, Nat.mod_eq_of_lt x.bv.isLt]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.bv.isLt)]

/-- The class-1 square of every word operation. -/
theorem WordOp.square {ty : UScalarTy} (o : WordOp) (x y : UScalar ty) :
    RCompOk EncRel (o.aen x y) (pure (o.rt ty.numBits (enc x) (enc y)) : Id Int) := by
  cases o
  · exact bitand_w_u_square x y
  · exact bitor_w_u_square x y
  · exact bitxor_w_u_square x y
  · exact wrapping_add_w_u_square x y
  · exact wrapping_sub_w_u_square x y
  · exact wrapping_mul_w_u_square x y
  · exact shr_w_u_square x y
  · exact shl_w_u_square x y
  · simp only [WordOp.aen, WordOp.rt]
    split
    · rename_i h
      have hs := rotate_right_w_u_square x (UScalar.ofNatCore (ty := .U32) y.val h)
      have he : enc (UScalar.ofNatCore (ty := .U32) y.val h) = enc y := rfl
      rwa [he] at hs
    · rw [rcompOk_iff]
      intro a ha
      cases ha
  · simp only [WordOp.aen, WordOp.rt]
    split
    · rename_i h
      have hs := rotate_left_w_u_square x (UScalar.ofNatCore (ty := .U32) y.val h)
      have he : enc (UScalar.ofNatCore (ty := .U32) y.val h) = enc y := rfl
      rwa [he] at hs
    · rw [rcompOk_iff]
      intro a ha
      cases ha

/-- An integer literal read at `ty`: its scalar when it is in range. -/
def litA (ty : UScalarTy) (n : Int) : RustM (UScalar ty) :=
  if h : 0 ≤ n ∧ n.toNat < 2 ^ ty.numBits then .ok (UScalar.ofNatCore n.toNat h.2)
  else .fail .undef

/-- The environment `ρ` with `x` bound to `a`. -/
def updEnv {α : Type} (ρ : String → α) (x : String) (a : α) : String → α :=
  fun y => if y = x then a else ρ y

/-- The Aeneas reading of a literal of the word fragment at width `ty`. -/
def toRustM (ty : UScalarTy) : Hax.ImpExpr → (String → Option (UScalar ty)) →
    RustM (UScalar ty)
  | .lit (.int n), _ => litA ty n
  | .var x, ρ => match ρ x with
    | some v => .ok v
    | none => .fail .undef
  | .letBind x v b, ρ => do
    let a ← toRustM ty v ρ
    toRustM ty b (updEnv ρ x (some a))
  | .app f [a, b], ρ => match WordOp.ofName (uTag ty) f with
    | some o => do
      let x ← toRustM ty a ρ
      let y ← toRustM ty b ρ
      o.aen x y
    | none => .fail .undef
  | .app f [a], ρ => if f = "Not#" ++ uTag ty then do
      let x ← toRustM ty a ρ
      lift (~~~x)
    else .fail .undef
  | .typeAscription e _, ρ => toRustM ty e ρ
  | _, _ => .fail .undef

/-- The runtime reading of a literal of the word fragment at width `ty`, over unbounded
    integers. Outside the fragment it returns `0`; `toRustM` fails there. -/
def runWord (ty : UScalarTy) : Hax.ImpExpr → (String → Int) → Int
  | .lit (.int n), _ => n
  | .var x, ρ => ρ x
  | .letBind x v b, ρ => runWord ty b (updEnv ρ x (runWord ty v ρ))
  | .app f [a, b], ρ => match WordOp.ofName (uTag ty) f with
    | some o => o.rt ty.numBits (runWord ty a ρ) (runWord ty b ρ)
    | none => 0
  | .app _ [a], ρ => Hax.bitnot_w ty.numBits (runWord ty a ρ)
  | .typeAscription e _, ρ => runWord ty e ρ
  | _, _ => 0

/-- An Aeneas environment and a runtime environment related by the encoding: every bound
    Aeneas scalar is encoded by the runtime value at its name. -/
def EnvRel {ty : UScalarTy} (ρA : String → Option (UScalar ty)) (ρI : String → Int) : Prop :=
  ∀ x a, ρA x = some a → ρI x = enc a

theorem envRel_updEnv {ty : UScalarTy} {ρA : String → Option (UScalar ty)} {ρI : String → Int}
    (h : EnvRel ρA ρI) (x : String) (a : UScalar ty) :
    EnvRel (updEnv ρA x (some a)) (updEnv ρI x (enc a)) := by
  intro y b hy
  unfold updEnv at hy ⊢
  split
  · rename_i hxy
    rw [ite_eq_left hxy] at hy
    cases hy
    rfl
  · rename_i hxy
    rw [ite_eq_right hxy] at hy
    exact h y b hy

theorem litA_ok {ty : UScalarTy} {n : Int} {r : UScalar ty} (h : litA ty n = .ok r) :
    enc r = n := by
  unfold litA at h
  split at h
  · rename_i hn
    cases h
    simp only [enc_uscalar, UScalar.val, UScalar.ofNatCore]
    simp only [BitVec.toNat_ofFin]
    omega
  · cases h

/-- **The pasting lemma**, in the form of an implication: every value the Aeneas reading
    returns encodes the runtime reading. -/
theorem toRustM_ok {ty : UScalarTy} (e : Hax.ImpExpr) (ρA : String → Option (UScalar ty)) :
    ∀ ρI : String → Int, EnvRel ρA ρI → ∀ r, toRustM ty e ρA = .ok r →
      enc r = runWord ty e ρI := by
  fun_induction toRustM ty e ρA with
  | case1 n ρA =>
    intro ρI _ r h
    simp only [runWord]
    exact litA_ok h
  | case2 x ρA v hv =>
    intro ρI hρ r h
    simp only [RustM.ok.injEq] at h
    subst h
    simp only [runWord]
    exact (hρ x v hv).symm
  | case3 x ρA hv =>
    intro ρI _ r h
    cases h
  | case4 x v b ρA ihv ihb =>
    intro ρI hρ r h
    simp only [runWord]
    cases hv : toRustM ty v ρA with
    | ok a =>
      rw [hv] at h
      have ha := ihv ρI hρ a hv
      rw [← ha]
      exact ihb a _ (envRel_updEnv hρ x a) r h
    | fail _ => rw [hv] at h; cases h
    | div => rw [hv] at h; cases h
  | case5 f a b ρA o ho iha ihb =>
    intro ρI hρ r h
    simp only [runWord, ho]
    cases hx : toRustM ty a ρA with
    | ok x =>
      rw [hx] at h
      cases hy : toRustM ty b ρA with
      | ok y =>
        rw [hy] at h
        rw [← iha ρI hρ x hx, ← ihb ρI hρ y hy]
        exact rcompOk_iff.mp (WordOp.square o x y) r h
      | fail _ => rw [hy] at h; cases h
      | div => rw [hy] at h; cases h
    | fail _ => rw [hx] at h; cases h
    | div => rw [hx] at h; cases h
  | case6 f a b ρA ho =>
    intro ρI _ r h
    cases h
  | case7 a ρA iha =>
    intro ρI hρ r h
    simp only [runWord]
    cases hx : toRustM ty a ρA with
    | ok x =>
      rw [hx] at h
      rw [← iha ρI hρ x hx]
      exact rcompOk_iff.mp (bitnot_w_u_square x) r h
    | fail _ => rw [hx] at h; cases h
    | div => rw [hx] at h; cases h
  | case8 f a ρA hf =>
    intro ρI _ r h
    cases h
  | case9 e s ρA ih =>
    intro ρI hρ r h
    simp only [runWord]
    exact ih ρI hρ r h
  | case10 t ρA h1 h2 h3 h4 h5 h6 =>
    intro ρI _ r h
    cases t <;> simp_all

/-- **The pasting lemma.** For environments related by the encoding, the Aeneas reading
    of a literal of the word fragment and its runtime reading form a square. -/
theorem toRustM_square {ty : UScalarTy} (e : Hax.ImpExpr) {ρA : String → Option (UScalar ty)}
    {ρI : String → Int} (hρ : EnvRel ρA ρI) :
    RCompOk EncRel (toRustM ty e ρA) (pure (runWord ty e ρI) : Id Int) :=
  rcompOk_iff.mpr (toRustM_ok e ρA ρI hρ)

/-- The value of an integer literal. -/
def litVal? : Hax.ImpExpr → Option Int
  | .lit (.int n) => some n
  | _ => none

theorem eq_of_litVal? {b : Hax.ImpExpr} {n : Int} (h : litVal? b = some n) :
    b = .lit (.int n) := by
  unfold litVal? at h
  split at h
  · cases h; rfl
  · cases h

/-- The amount check of an operation: a shift amount is a literal below the width, a
    rotation amount a literal below `2 ^ 32`; the other operations take any operand. -/
def WordOp.amountOk (w : Nat) (o : WordOp) (b : Hax.ImpExpr) : Bool :=
  match o, litVal? b with
  | .shr, some n | .shl, some n => decide (0 ≤ n ∧ n < w)
  | .rotr, some n | .rotl, some n => decide (0 ≤ n ∧ n < 2 ^ 32)
  | .shr, none | .shl, none | .rotr, none | .rotl, none => false
  | _, _ => true

/-- The check under which the Aeneas reading returns a value: every construct is in the
    word fragment, every literal is in range, every shift and rotation amount passes
    `WordOp.amountOk`, and every variable read is in `bound` or bound by an enclosing
    `let`. -/
def totalOk (ty : UScalarTy) : Hax.ImpExpr → (String → Bool) → Bool
  | .lit (.int n), _ => decide (0 ≤ n ∧ n.toNat < 2 ^ ty.numBits)
  | .var x, bound => bound x
  | .letBind x v b, bound => totalOk ty v bound && totalOk ty b (updEnv bound x true)
  | .app f [a, b], bound => match WordOp.ofName (uTag ty) f with
    | some o => totalOk ty a bound && totalOk ty b bound && o.amountOk ty.numBits b
    | none => false
  | .app f [a], bound => decide (f = "Not#" ++ uTag ty) && totalOk ty a bound
  | .typeAscription e _, bound => totalOk ty e bound
  | _, _ => false

theorem litA_isOk {ty : UScalarTy} {n : Int} (h : 0 ≤ n ∧ n.toNat < 2 ^ ty.numBits) :
    ∃ r, litA ty n = .ok r := by
  unfold litA
  rw [dite_eq_left h]
  exact ⟨_, rfl⟩

/-- An operation returns a value when its amount passes `WordOp.amountOk`. -/
theorem WordOp.aen_isOk {ty : UScalarTy} (o : WordOp) (b : Hax.ImpExpr)
    (hb : o.amountOk ty.numBits b = true) (x y : UScalar ty)
    (hy : ∀ n, litVal? b = some n → (y.val : Int) = n) :
    ∃ r, o.aen x y = .ok r := by
  cases o
  case band | bor | bxor | wadd | wsub | wmul => exact ⟨_, rfl⟩
  all_goals
    unfold WordOp.amountOk at hb
    obtain ⟨n, hl⟩ : ∃ n, litVal? b = some n := by
      cases hl : litVal? b with
      | none => rw [hl] at hb; cases hb
      | some n => exact ⟨n, rfl⟩
    rw [hl] at hb
    have hyn := hy n hl
    simp only [decide_eq_true_eq] at hb
  · refine ⟨⟨x.bv.ushiftRight y.val⟩, ?_⟩
    show UScalar.shiftRight x y.val = _
    unfold UScalar.shiftRight
    rw [ite_eq_left (by omega)]
  · refine ⟨⟨x.bv.shiftLeft y.val⟩, ?_⟩
    show UScalar.shiftLeft x y.val = _
    unfold UScalar.shiftLeft
    rw [ite_eq_left (by omega)]
  · have h32 : y.val < 2 ^ UScalarTy.U32.numBits := by
      simp only [UScalarTy.U32_numBits_eq]; omega
    exact ⟨_, dite_eq_left h32⟩
  · have h32 : y.val < 2 ^ UScalarTy.U32.numBits := by
      simp only [UScalarTy.U32_numBits_eq]; omega
    exact ⟨_, dite_eq_left h32⟩

theorem updEnv_bound {ty : UScalarTy} {ρA : String → Option (UScalar ty)}
    {bound : String → Bool} (hb : ∀ x, bound x = true → ∃ v, ρA x = some v)
    (x : String) (a : UScalar ty) :
    ∀ y, updEnv bound x true y = true → ∃ v, updEnv ρA x (some a) y = some v := by
  intro y hy
  unfold updEnv at hy ⊢
  split
  · exact ⟨a, rfl⟩
  · rename_i hxy
    rw [ite_eq_right hxy] at hy
    exact hb y hy

/-- **The reading returns a value** on an expression that passes `totalOk` from an
    environment binding every name of `bound`. -/
theorem toRustM_isOk_of_totalOk {ty : UScalarTy} (e : Hax.ImpExpr)
    (ρA : String → Option (UScalar ty)) :
    ∀ bound : String → Bool, totalOk ty e bound = true →
      (∀ x, bound x = true → ∃ v, ρA x = some v) → ∃ r, toRustM ty e ρA = .ok r := by
  fun_induction toRustM ty e ρA with
  | case1 n ρA =>
    intro bound h _
    simp only [totalOk, decide_eq_true_eq] at h
    exact litA_isOk h
  | case2 x ρA v hv =>
    intro _ _ _
    exact ⟨v, rfl⟩
  | case3 x ρA hv =>
    intro bound h hb
    simp only [totalOk] at h
    obtain ⟨v, hv'⟩ := hb x h
    rw [hv] at hv'
    cases hv'
  | case4 x v b ρA ihv ihb =>
    intro bound h hb
    simp only [totalOk, Bool.and_eq_true] at h
    obtain ⟨a, ha⟩ := ihv bound h.1 hb
    obtain ⟨r, hr⟩ := ihb a (updEnv bound x true) h.2 (updEnv_bound hb x a)
    exact ⟨r, by rw [ha]; exact hr⟩
  | case5 f a b ρA o ho iha ihb =>
    intro bound h hb
    simp only [totalOk, ho, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := iha bound h.1.1 hb
    obtain ⟨y, hy⟩ := ihb bound h.1.2 hb
    have hyv : ∀ n, litVal? b = some n → (y.val : Int) = n := by
      intro n hn
      have hb' := eq_of_litVal? hn
      subst hb'
      exact litA_ok hy
    obtain ⟨r, hr⟩ := o.aen_isOk b h.2 x y hyv
    exact ⟨r, by rw [hx]; show (toRustM ty b ρA >>= fun y => o.aen x y) = _; rw [hy]; exact hr⟩
  | case6 f a b ρA ho =>
    intro bound h _
    simp only [totalOk, ho] at h
    cases h
  | case7 a ρA iha =>
    intro bound h hb
    simp only [totalOk, Bool.and_eq_true] at h
    obtain ⟨x, hx⟩ := iha bound h.2 hb
    exact ⟨_, by rw [hx]; rfl⟩
  | case8 f a ρA hf =>
    intro bound h _
    simp only [totalOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact absurd h.1 hf
  | case9 e s ρA ih =>
    intro bound h hb
    simp only [totalOk] at h
    exact ih bound h hb
  | case10 t ρA h1 h2 h3 h4 h5 h6 =>
    intro bound h _
    unfold totalOk at h
    split at h <;> simp_all

/-- **The Aeneas reading of a function, composed with its ascent correspondence.** When the
    surface function `f` of an ascent correspondence is the runtime reading of its literal
    over the environments `ρI a`, every value `r` the Aeneas reading returns over an
    environment related to `ρI a` is, from some fuel on, the value of the run of the literal:
    `.int (enc r)`. -/
theorem fnCorres_toRustM {ty : UScalarTy} {bi : Hax.Builtins} {A : Type} {e : Hax.ImpExpr}
    {entry : A → Hax.Env} {G : A → Prop} {f : A → Int}
    (hF : Hax.Ascent.FnCorres bi e entry G f) (ρI : A → String → Int)
    (hbr : ∀ a, runWord ty e (ρI a) = f a)
    (a : A) (hG : G a) (ρA : String → Option (UScalar ty)) (hρ : EnvRel ρA (ρI a))
    (r : UScalar ty) (hr : toRustM ty e ρA = .ok r) :
    ∃ fuel₀, ∀ fuel, fuel₀ ≤ fuel → (Hax.denote' bi fuel e (entry a)).1 = .val (.int (enc r)) := by
  obtain ⟨fuel₀, hrun⟩ := hF a hG
  refine ⟨fuel₀, fun fuel hf => ?_⟩
  rw [hrun fuel hf, toRustM_ok e ρA (ρI a) hρ r hr, hbr]
  rfl

end CatCrypt.Hax.RustSemantics
