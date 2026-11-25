/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.AeneasFront.NFToRustM
public import CatCrypt.Crypto.SecureCompilation.VIR.NFRangeLoop

/-!
# Soundness of the name specification of the Aeneas reading

`aeSpec_sound` states that the name specification `NFRange.aeSpec` of the interval checker is
sound for the leaf table `aeTable` of the Aeneas reading (`AeneasFront/NFToRustM.lean`): a
call whose transfer function accepts abstract arguments that hold of the concrete arguments
returns a value, with no failure, that its abstract result holds of; a comparison name answers
with its comparison and a connective name with its connective. With it, `NFRange.check_sound'`
applies to the Aeneas reading.

A word argument of a tagged name is read as an Aeneas word of the width of the tag; the
transfer function accepts it only when its interval lies below `2 ^ b` for the width `b` the
tag is read at, which is at most the width of the Aeneas word (the tag `size` is read at `32`
bits, at most the width of `usize`).

## Main results

* `RangeSpec.wordXfer_sound`, `RangeSpec.checkedXfer_sound`: the intervals of the word and
  checked operations hold the values of the Aeneas operations, which do not fail.
* `RangeSpec.aeXfer1_sound`, `RangeSpec.aeXfer2_sound`, `RangeSpec.aeXfer3_sound`: the
  transfer functions of the unary, binary and ternary names.
* `aeSpec_sound`: `aeSpec.SoundAt aeTable`.
-/

public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.AeneasFront

open HaxLean.Aeneas.Std
open _root_.Hax (Value)
open CatCrypt.Hax.RustSemantics (WordOp AOp wordOpAt? checkedAt? tagTyAt? uTag litA
  rustM_bind_ok)
open CatCrypt.Crypto.Hax
open CatCrypt.Crypto.Hax.ImpToNF (enc dec encAll)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.NFRange
open CatCrypt.Crypto.SecureCompilation.RangeDomain
open HaxLean.Aeneas.Std.WP (spec_imp_exists)

namespace RangeSpec

/-! ## The operations of the reading named by the checker -/

/-- The word operation of the reading that a tagged word operation of the checker names. -/
def aeWordOpW : AeWordOp → WordOp
  | .band => .band
  | .bor => .bor
  | .bxor => .bxor
  | .wadd => .wadd
  | .wsub => .wsub
  | .wmul => .wmul
  | .shr => .shr
  | .shl => .shl
  | .rotr => .rotr
  | .rotl => .rotl

/-- The checked operation of the reading that a checked operation of the checker names. -/
def aeCheckedA : AeChecked → AOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul

/-! ## Values -/

theorem usize_ge_32 : 32 ≤ UScalarTy.Usize.numBits := by
  rcases System.Platform.numBits_eq with h | h <;> simp [h]

theorem readW_nat {ty : UScalarTy} {n : Nat} (h : n < 2 ^ ty.numBits) :
    ∃ u : UScalar ty, readW ty (.int (n : Int)) = .ok u ∧ u.val = n := by
  refine ⟨UScalar.ofNatCore n h, ?_, ?_⟩
  · simp [readW, litA, h]
  · simp

theorem dec_word {w n : Nat} (h : n < 2 ^ w) :
    ∃ y : BitVec w, dec (.word w) (.int (n : Int)) = some y ∧ y.toNat = n := by
  have h' : (n : Int) < 2 ^ w := by exact_mod_cast h
  refine ⟨BitVec.ofNat w n, ?_, ?_⟩
  · simp [dec, h']
  · simp [Nat.mod_eq_of_lt h]

theorem lt_of_below {b : Nat} {i : Iv} {n : Nat} (hb : below b i = true) (hn : i.Has n) :
    n < 2 ^ b := by
  have h1 : (n : Int) < 2 ^ b := lt_of_le_of_lt hn.2 (by simpa [below] using hb)
  exact_mod_cast h1

theorem has_nn {i : Iv} {n : Nat} (h : i.Has n) : (nn i).Has n := by
  unfold Iv.Has nn at *
  omega

theorem nn_fst (i : Iv) : 0 ≤ (nn i).1 := by
  simp [nn]

theorem retWord_spec {r : NfTy} {I : Iv} {a : AVal r} (h : retWord r I = some a) {n : Nat}
    (hn : I.Has n) : ∃ y, dec r (.int (n : Int)) = some y ∧ AVal.Mem r a y := by
  cases r with
  | word w =>
    simp only [retWord] at h
    split at h
    · rename_i hb
      cases h
      obtain ⟨y, hy, hyn⟩ := dec_word (lt_of_below hb hn)
      refine ⟨y, hy, ?_⟩
      simp only [AVal.Mem, hyn]
      exact hn
    · cases h
  | _ => simp [retWord] at h

theorem retBit_spec {r : NfTy} {p : ABit} {a : AVal r} (h : retBit r p = some a) {b : Bool}
    (hb : p.val = none ∨ p.val = some b) : ∃ y, dec r (.bool b) = some y ∧ AVal.Mem r a y := by
  cases r with
  | bit =>
    simp only [retBit, Option.some.injEq] at h
    subst h
    exact ⟨b, rfl, hb⟩
  | _ => simp [retBit] at h

theorem wordArg_spec {t : NfTy} {x : AVal t} {xv : t.denote} {i : Iv}
    (h : wordArg t x = some i) (hm : AVal.Mem t x xv) :
    ∃ n : Nat, enc t xv = .int (n : Int) ∧ i.Has n := by
  cases t with
  | word w =>
    simp only [wordArg, Option.some.injEq] at h
    subst h
    exact ⟨xv.toNat, rfl, hm⟩
  | _ => simp [wordArg] at h

theorem bitArg_spec {t : NfTy} {x : AVal t} {xv : t.denote} {p : ABit}
    (h : bitArg t x = some p) (hm : AVal.Mem t x xv) :
    ∃ b : Bool, enc t xv = .bool b ∧ (p.val = none ∨ p.val = some b) := by
  cases t with
  | bit =>
    simp only [bitArg, Option.some.injEq] at h
    subst h
    exact ⟨xv, rfl, hm⟩
  | _ => simp [bitArg] at h

theorem arrArg_spec {t : NfTy} {x : AVal t} {xv : t.denote} {n : Nat} {e : Iv}
    (h : arrArg t x = some (n, e)) (hm : AVal.Mem t x xv) :
    ∃ ns : List Nat, enc t xv = .array (ns.map fun (k : Nat) => Value.int (k : Int)) ∧
      ns.length = n ∧
      ∀ k ∈ ns, e.Has k := by
  cases t with
  | arr m s =>
    cases s with
    | word w =>
      simp only [arrArg, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨List.ofFn fun j => (xv j).toNat, ?_, by simp, ?_⟩
      · simp [enc, List.map_ofFn]
        rfl
      · intro k hk
        simp only [List.mem_ofFn] at hk
        obtain ⟨j, rfl⟩ := hk
        exact hm j
    | _ => simp [arrArg] at h
  | _ => simp [arrArg] at h

theorem readWs_nats : ∀ (ns : List Nat), (∀ k ∈ ns, k < 2 ^ 64) →
    ∃ us : List U64, readWs (ns.map fun (k : Nat) => Value.int (k : Int)) = .ok us ∧
      us.map UScalar.val = ns
  | [], _ => ⟨[], rfl, rfl⟩
  | k :: ns, h => by
    obtain ⟨u, hu, huv⟩ := readW_nat (ty := .U64) (h k (by simp))
    obtain ⟨us, hus, husv⟩ := readWs_nats ns (fun k hk => h k (by simp [hk]))
    refine ⟨u :: us, ?_, by simp [huv, husv]⟩
    simp [readWs, hu, hus]

theorem mapM_dec_word {w : Nat} : ∀ (zs : List Nat), (∀ k ∈ zs, k < 2 ^ w) →
    ∃ ys : List (BitVec w),
      (zs.map fun (k : Nat) => Value.int (k : Int)).mapM (dec (.word w)) = some ys ∧
      ys.map BitVec.toNat = zs
  | [], _ => ⟨[], rfl, rfl⟩
  | k :: zs, h => by
    obtain ⟨y, hy, hyv⟩ := dec_word (h k (by simp))
    obtain ⟨ys, hys, hysv⟩ := mapM_dec_word zs (fun k hk => h k (by simp [hk]))
    refine ⟨y :: ys, ?_, by simp [hyv, hysv]⟩
    simp [List.mapM_cons, hy, hys]

/-! ## The leaf table on a call that succeeds -/

theorem aeTable_call_of_ok {f : String} {as : List NfTy} {r : NfTy}
    {xs : HVector NfTy.denote as} {v : Value} (h : aeCallV f (encAll as xs) = .ok v) :
    aeTable.call f as r xs = dec r v := by
  change (match aeCallV f (encAll as xs) with | .ok v => dec r v | _ => none) = _
  rw [h]

theorem aeTable_call_ok {f : String} {as : List NfTy} {r : NfTy}
    {xs : HVector NfTy.denote as} {y : r.denote} (h : aeTable.call f as r xs = some y) :
    ∃ v, aeCallV f (encAll as xs) = .ok v ∧ dec r v = some y := by
  change (match aeCallV f (encAll as xs) with | .ok v => dec r v | _ => none) = _ at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · cases h

/-! ## The names -/

theorem wordOpAt?_opName (ty : UScalarTy) (o : WordOp) :
    wordOpAt? (opName o ++ uTag ty) = some (ty, o) := by
  cases ty <;> cases o <;> decide +kernel

theorem aeCall2_opName {ty : UScalarTy} {o : WordOp} (hw : wordAt ty o = true) (a b : Value) :
    aeCall2 (opName o ++ uTag ty) a b =
      (readW ty a >>= fun x => readW ty b >>= fun y => o.aen x y >>= fun z => .ok (wordV z)) := by
  unfold aeCall2
  rw [wordOpAt?_opName]
  simp only [hw, ite_true]

theorem aeCall2_checkedName {ty : UScalarTy} (hty : checkedTy ty = true) (o : AOp)
    (ho : taggedOp o = true) (a b : Value) :
    aeCall2 (checkedName o ty) a b =
      (readW ty a >>= fun x => readW ty b >>= fun y => o.aen x y >>= fun z => .ok (wordV z)) := by
  have hw : wordOpAt? (checkedName o ty) = none := by
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd hty (by decide) | decide +kernel
  have hc : checkedAt? (checkedName o ty) = some (ty, o) := by
    cases o <;> simp [taggedOp] at ho <;> cases ty <;>
      first | exact absurd hty (by decide) | decide +kernel
  unfold aeCall2
  rw [hw, hc]
  simp only [hty, ho, Bool.and_self, ite_true]

theorem aeCall2_cmpName (c : CmpOp) (a b : Value) :
    aeCall2 c.name a b =
      (readW .U64 a >>= fun x => readW .U64 b >>= fun y => .ok (.bool (c.aen x y))) := by
  have hw : wordOpAt? c.name = none := by cases c <;> decide +kernel
  have hc : checkedAt? c.name = none := by cases c <;> decide +kernel
  have hn : CmpOp.ofName? c.name = some c := by cases c <;> decide +kernel
  unfold aeCall2
  rw [hw, hc, hn]

theorem aeCall2_boolName (o : BoolOp) (a b : Value) :
    aeCall2 o.name a b =
      (readB a >>= fun p => readB b >>= fun q => .ok (.bool (o.val p q))) := by
  have hw : wordOpAt? o.name = none := by cases o <;> decide +kernel
  have hc : checkedAt? o.name = none := by cases o <;> decide +kernel
  have hn : CmpOp.ofName? o.name = none := by cases o <;> decide +kernel
  have hb : BoolOp.ofName? o.name = some o := by cases o <;> decide +kernel
  unfold aeCall2
  rw [hw, hc, hn, hb]

theorem aeCall2_index (a b : Value) :
    aeCall2 "index" a b =
      (readArr a >>= fun arr => readW .Usize b >>= fun i =>
        arr.2.index_usize i >>= fun z => .ok (wordV z)) := by
  have hw : wordOpAt? "index" = none := by decide +kernel
  have hc : checkedAt? "index" = none := by decide +kernel
  have hn : CmpOp.ofName? "index" = none := by decide +kernel
  have hb : BoolOp.ofName? "index" = none := by decide +kernel
  unfold aeCall2
  rw [hw, hc, hn, hb]
  simp

theorem aeWordName?_spec {f : String} {o : AeWordOp} {b : Nat}
    (h : aeWordName? f = some (o, b)) :
    ∃ ty, f = opName (aeWordOpW o) ++ uTag ty ∧ wordAt ty (aeWordOpW o) = true ∧
      b ≤ ty.numBits ∧ (b = ty.numBits ∨ o.atSize = true) := by
  have hU := usize_ge_32
  obtain ⟨⟨tag, b'⟩, ht, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨⟨pre, o'⟩, ho, h2⟩ := List.exists_of_findSome?_eq_some h1
  simp only [aeTags, aeWordOps, List.mem_cons, List.not_mem_nil, Prod.mk.injEq,
    or_false] at ht ho
  simp only at h2
  clear h h1
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨.U8, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [opName, uTag, wordAt, tableTy, aeWordOpW]
  · refine ⟨.U16, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [opName, uTag, wordAt, tableTy, aeWordOpW]
  · refine ⟨.U32, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [opName, uTag, wordAt, tableTy, aeWordOpW]
  · refine ⟨.U64, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [opName, uTag, wordAt, tableTy, aeWordOpW]
  · refine ⟨.Usize, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [opName, uTag, wordAt, tableTy, widthFree, aeWordOpW,
      AeWordOp.atSize]

/-! ## The word and checked operations -/

theorem ediv_two_pow_le {a b : Int} {m k : Nat} (ha : 0 ≤ a) (hab : a ≤ b) (hmk : m ≤ k) :
    a / 2 ^ k ≤ b / 2 ^ m := by
  have h1 : a / 2 ^ k ≤ a / 2 ^ m := by
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    have h3 : ((n / 2 ^ k : Nat) : Int) ≤ ((n / 2 ^ m : Nat) : Int) := by
      exact_mod_cast Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) hmk)
        (by positivity)
    simpa using h3
  have h2 : a / 2 ^ m ≤ b / 2 ^ m := Int.ediv_le_ediv (by positivity) hab
  omega

theorem mul_two_pow_le {a b : Int} {m k : Nat} (ha : 0 ≤ a) (hab : a ≤ b) (hmk : m ≤ k) :
    a * 2 ^ m ≤ b * 2 ^ k :=
  mul_le_mul hab (pow_le_pow_right₀ (by norm_num) hmk) (by positivity) (by omega)

/-- The exclusive or of a number below `2 ^ k` with `2 ^ k` is their sum. -/
theorem xor_two_pow_of_lt {x k : Nat} (h : x < 2 ^ k) : x ^^^ 2 ^ k = x + 2 ^ k := by
  have h1 := Nat.two_pow_add_eq_or_of_lt h 1
  have h3 : x ^^^ 2 ^ k = 2 ^ k * 1 ||| x := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_or, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hi : k = i
    · subst hi
      simp [Nat.testBit_lt_two_pow h]
    · simp [hi]
  omega

/-- The exclusive or of `a` and `b` divided by `2 ^ k` is the exclusive or of the quotients. -/
theorem xor_div_two_pow (a b k : Nat) : (a ^^^ b) / 2 ^ k = a / 2 ^ k ^^^ b / 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]

/-- **The exclusive or keeps the agreeing high bits**: for `a` in `[x₁, x₂]` and `b` in
    `[y₁, y₂]`, where the bounds of each agree above the bit `k`, the exclusive or of `a` and `b`
    has above `k` the exclusive or of the high bits of the bounds. -/
theorem xor_mem_prefix {k a b x₁ x₂ y₁ y₂ : Nat} (ha : x₁ ≤ a ∧ a ≤ x₂) (hb : y₁ ≤ b ∧ b ≤ y₂)
    (hx : x₁ / 2 ^ k = x₂ / 2 ^ k) (hy : y₁ / 2 ^ k = y₂ / 2 ^ k) :
    (x₁ / 2 ^ k ^^^ y₁ / 2 ^ k) * 2 ^ k ≤ a ^^^ b ∧
      a ^^^ b < (x₁ / 2 ^ k ^^^ y₁ / 2 ^ k) * 2 ^ k + 2 ^ k := by
  have hak : a / 2 ^ k = x₁ / 2 ^ k :=
    Nat.le_antisymm (hx ▸ Nat.div_le_div_right ha.2) (Nat.div_le_div_right ha.1)
  have hbk : b / 2 ^ k = y₁ / 2 ^ k :=
    Nat.le_antisymm (hy ▸ Nat.div_le_div_right hb.2) (Nat.div_le_div_right hb.1)
  have hq : (a ^^^ b) / 2 ^ k = x₁ / 2 ^ k ^^^ y₁ / 2 ^ k := by
    rw [xor_div_two_pow, hak, hbk]
  have hd := Nat.div_add_mod (a ^^^ b) (2 ^ k)
  have hm := Nat.mod_lt (a ^^^ b) (Nat.two_pow_pos k)
  rw [hq] at hd
  generalize x₁ / 2 ^ k ^^^ y₁ / 2 ^ k = Q at hd ⊢
  generalize (a ^^^ b) % 2 ^ k = r at hd hm
  rw [Nat.mul_comm] at hd
  omega

/-- The interval of `xorPrefix` holds the exclusive or of the values of nonnegative intervals
    whose bounds agree above the bit `k`. -/
theorem has_xor_prefix {k : Nat} {i j : Iv} {x y : Nat} (hx : i.Has x) (hy : j.Has y)
    (hc : i.1.toNat / 2 ^ k = i.2.toNat / 2 ^ k ∧ j.1.toNat / 2 ^ k = j.2.toNat / 2 ^ k) :
    Iv.Has ((((i.1.toNat / 2 ^ k ^^^ j.1.toNat / 2 ^ k) * 2 ^ k : Nat) : Int),
      (((i.1.toNat / 2 ^ k ^^^ j.1.toNat / 2 ^ k) * 2 ^ k : Nat) : Int) + 2 ^ k - 1)
      ((x ^^^ y : Nat) : Int) := by
  unfold Iv.Has at hx hy ⊢
  have h := xor_mem_prefix (k := k) (a := x) (b := y) (x₁ := i.1.toNat) (x₂ := i.2.toNat)
    (y₁ := j.1.toNat) (y₂ := j.2.toNat) (by omega) (by omega) hc.1 hc.2
  have hk : ((2 : Int) ^ k) = ((2 ^ k : Nat) : Int) := by push_cast; rfl
  rw [hk]
  generalize (i.1.toNat / 2 ^ k ^^^ j.1.toNat / 2 ^ k) * 2 ^ k = P at h ⊢
  generalize 2 ^ k = K at h ⊢
  omega

/-- The interval of the exclusive or of words of nonnegative intervals that `wordXfer` gives
    when the second is not a power of two above the first: the agreeing high bits of the bounds
    (`xorPrefix`), below the power of two above both upper bounds and below `2 ^ b`. -/
theorem has_xor_rest {b : Nat} {i j I : Iv} {x y : Nat}
    (hx : i.Has x) (hy : j.Has y) (hxb : x < 2 ^ b) (hyb : y < 2 ^ b)
    (h : (match xorPrefix (xorPrefixBit i j) i j with
      | some I => some (I.1, min I.2 (min (2 ^ b - 1)
          (2 ^ (Nat.log2 (max i.2 j.2).toNat + 1) - 1)))
      | none => some (0, min (2 ^ b - 1) (2 ^ (Nat.log2 (max i.2 j.2).toNat + 1) - 1))) =
      some I) :
    I.Has ((x ^^^ y : Nat) : Int) := by
  have hM := Nat.lt_log2_self (n := (max i.2 j.2).toNat)
  unfold Iv.Has at hx hy
  have hxM : x < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by omega
  have hyM : y < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by omega
  have h1 : ((x ^^^ y : Nat) : Int) < 2 ^ b := by
    exact_mod_cast Nat.xor_lt_two_pow hxb hyb
  have h2 : ((x ^^^ y : Nat) : Int) < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by
    exact_mod_cast Nat.xor_lt_two_pow hxM hyM
  split at h
  · rename_i J hJ
    cases h
    unfold xorPrefix at hJ
    split_ifs at hJ with hc
    cases hJ
    have hp := has_xor_prefix (x := x) (y := y) hx hy hc
    unfold Iv.Has at hp ⊢
    omega
  · cases h
    unfold Iv.Has
    omega

/-- The interval `wordXfer` gives a tagged word operation at a width `b` at most the width of
    the Aeneas words holds the value of the Aeneas operation, which does not fail. -/
theorem wordXfer_sound {ty : UScalarTy} {o : AeWordOp} {b : Nat} (hble : b ≤ ty.numBits)
    (hbo : b = ty.numBits ∨ o.atSize = true) {i j I : Iv} (hi0 : 0 ≤ i.1) (hj0 : 0 ≤ j.1)
    (x y : UScalar ty) (hx : i.Has x.val) (hy : j.Has y.val) (hxb : x.val < 2 ^ b)
    (hyb : y.val < 2 ^ b) (h : wordXfer o b i j = some I) :
    ∃ z, (aeWordOpW o).aen x y = .ok z ∧ I.Has z.val := by
  have hbb : (2 : Int) ^ b ≤ 2 ^ ty.numBits := pow_le_pow_right₀ (by norm_num) hble
  have hxN : ((x.val : Nat) : Int) < 2 ^ ty.numBits := by exact_mod_cast x.hBounds
  have hyN : ((y.val : Nat) : Int) < 2 ^ ty.numBits := by exact_mod_cast y.hBounds
  unfold Iv.Has at hx hy
  cases o with
  | band =>
    simp only [wordXfer, Option.some.injEq] at h
    subst h
    refine ⟨x &&& y, rfl, ?_⟩
    have h1 : x.val &&& y.val ≤ x.val := Nat.and_le_left
    have h2 : x.val &&& y.val ≤ y.val := Nat.and_le_right
    simp only [UScalar.val_and]
    unfold Iv.Has
    omega
  | bor =>
    simp only [wordXfer, Option.some.injEq] at h
    subst h
    refine ⟨x ||| y, rfl, ?_⟩
    have hM := Nat.lt_log2_self (n := (max i.2 j.2).toNat)
    have hxM : x.val < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by omega
    have hyM : y.val < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by omega
    have h1 : ((x.val ||| y.val : Nat) : Int) < 2 ^ b := by
      exact_mod_cast Nat.or_lt_two_pow hxb hyb
    have h2 : ((x.val ||| y.val : Nat) : Int) < 2 ^ ((max i.2 j.2).toNat.log2 + 1) := by
      exact_mod_cast Nat.or_lt_two_pow hxM hyM
    simp only [UScalar.val_or]
    unfold Iv.Has
    omega
  | bxor =>
    simp only [wordXfer] at h
    split_ifs at h with hc
    · obtain ⟨h1, h2, h3⟩ := hc
      cases h
      refine ⟨x ^^^ y, rfl, ?_⟩
      have hyv : y.val = 2 ^ j.1.toNat.log2 := by
        have : ((y.val : Nat) : Int) = ((2 ^ j.1.toNat.log2 : Nat) : Int) := by push_cast; omega
        exact_mod_cast this
      have hxk : x.val < 2 ^ j.1.toNat.log2 := by
        have : ((x.val : Nat) : Int) < ((2 ^ j.1.toNat.log2 : Nat) : Int) := by push_cast; omega
        exact_mod_cast this
      simp only [UScalar.val_xor]
      rw [hyv, xor_two_pow_of_lt hxk]
      unfold Iv.Has
      push_cast
      omega
    refine ⟨x ^^^ y, rfl, ?_⟩
    rw [UScalar.val_xor]
    exact has_xor_rest hx hy hxb hyb h
  | wadd =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer, Option.some.injEq] at h
    subst h
    refine ⟨UScalar.wrapping_add x y, rfl, ?_⟩
    have hz : (((UScalar.wrapping_add x y).val : Nat) : Int) < 2 ^ ty.numBits := by
      exact_mod_cast (UScalar.wrapping_add x y).hBounds
    have hzv : (UScalar.wrapping_add x y).val = (x.val + y.val) % 2 ^ ty.numBits := by
      simp [UScalar.size]
    by_cases hs : (ivAddZ i j).2 < 2 ^ ty.numBits
    · simp only [hs, ↓reduceIte]
      simp only [ivAddZ] at hs ⊢
      have hlt : x.val + y.val < 2 ^ ty.numBits := by
        have : ((x.val + y.val : Nat) : Int) < 2 ^ ty.numBits := by push_cast; omega
        exact_mod_cast this
      rw [hzv, Nat.mod_eq_of_lt hlt]
      unfold Iv.Has
      push_cast
      grind
    simp only [hs, ↓reduceIte]
    by_cases hs2 : 2 ^ ty.numBits ≤ (ivAddZ i j).1
    · simp only [hs2, ↓reduceIte]
      simp only [ivAddZ] at hs hs2 ⊢
      have hge : 2 ^ ty.numBits ≤ x.val + y.val := by
        zify
        omega
      have hlt : x.val + y.val - 2 ^ ty.numBits < 2 ^ ty.numBits := by
        zify [hge]
        omega
      rw [hzv, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
      unfold Iv.Has
      push_cast [Nat.cast_sub hge]
      omega
    simp only [hs2, ↓reduceIte]
    unfold Iv.Has
    grind
  | wsub =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer, ivSubZ, Option.some.injEq] at h
    subst h
    refine ⟨UScalar.wrapping_sub x y, rfl, ?_⟩
    have hz : (((UScalar.wrapping_sub x y).val : Nat) : Int) < 2 ^ ty.numBits := by
      exact_mod_cast (UScalar.wrapping_sub x y).hBounds
    have hzv : (UScalar.wrapping_sub x y).val =
        (x.val + (2 ^ ty.numBits - y.val)) % 2 ^ ty.numBits := by
      simp [UScalar.size]
    split_ifs with hs
    · have hle : y.val ≤ x.val := by
        have : ((y.val : Nat) : Int) ≤ x.val := by omega
        exact_mod_cast this
      have hxl := x.hBounds
      have heq : x.val + (2 ^ ty.numBits - y.val) = (x.val - y.val) + 2 ^ ty.numBits := by
        omega
      rw [hzv, heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      unfold Iv.Has
      push_cast [hle]
      grind
    · unfold Iv.Has
      grind
  | wmul =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer, Option.some.injEq] at h
    subst h
    refine ⟨UScalar.wrapping_mul x y, rfl, ?_⟩
    have hz : (((UScalar.wrapping_mul x y).val : Nat) : Int) < 2 ^ ty.numBits := by
      exact_mod_cast (UScalar.wrapping_mul x y).hBounds
    have hzv : (UScalar.wrapping_mul x y).val = (x.val * y.val) % 2 ^ ty.numBits := by
      simp [UScalar.size]
    have hlo : i.1 * j.1 ≤ ((x.val : Nat) : Int) * ((y.val : Nat) : Int) :=
      mul_le_mul hx.1 hy.1 hj0 (by omega)
    have hhi : ((x.val : Nat) : Int) * ((y.val : Nat) : Int) ≤ i.2 * j.2 :=
      mul_le_mul hx.2 hy.2 (by omega) (by omega)
    split_ifs with hs
    · have hlt : x.val * y.val < 2 ^ ty.numBits := by
        have : ((x.val * y.val : Nat) : Int) < 2 ^ ty.numBits := by
          push_cast
          omega
        exact_mod_cast this
      rw [hzv, Nat.mod_eq_of_lt hlt]
      unfold Iv.Has
      push_cast
      omega
    · unfold Iv.Has
      omega
  | shr =>
    simp only [wordXfer] at h
    split at h
    · rename_i hjb
      simp only [Option.some.injEq] at h
      subst h
      have hyn : y.val < ty.numBits := by
        have : ((y.val : Nat) : Int) < ty.numBits := by omega
        exact_mod_cast this
      refine ⟨⟨x.bv.ushiftRight y.val⟩, ?_, ?_⟩
      · change UScalar.shiftRight x y.val = _
        simp [UScalar.shiftRight, hyn]
      have hzv' : (((⟨x.bv.ushiftRight y.val⟩ : UScalar ty).val : Nat) : Int) =
          ((x.val : Nat) : Int) / 2 ^ y.val := by
        change ((x.bv.toNat >>> y.val : Nat) : Int) = _
        rw [Nat.shiftRight_eq_div_pow]
        push_cast
        rfl
      have hy1 : y.val ≤ j.2.toNat := by omega
      have hy2 : j.1.toNat ≤ y.val := by omega
      unfold Iv.Has
      rw [hzv']
      exact ⟨ediv_two_pow_le hi0 hx.1 hy1, ediv_two_pow_le (by omega) hx.2 hy2⟩
    · cases h
  | shl =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer] at h
    split at h
    · rename_i hjb
      simp only [Option.some.injEq] at h
      subst h
      have hyn : y.val < ty.numBits := by
        have : ((y.val : Nat) : Int) < ty.numBits := by omega
        exact_mod_cast this
      refine ⟨⟨x.bv.shiftLeft y.val⟩, ?_, ?_⟩
      · change UScalar.shiftLeft x y.val = _
        simp [UScalar.shiftLeft, hyn]
      set z : UScalar ty := ⟨x.bv.shiftLeft y.val⟩ with hzdef
      have hzv : z.val = (x.val <<< y.val) % 2 ^ ty.numBits := by
        change (x.bv <<< y.val).toNat = _
        rw [BitVec.toNat_shiftLeft]
        rfl
      have hzN : (((z.val : Nat) : Int)) < 2 ^ ty.numBits := by exact_mod_cast z.hBounds
      have hy1 : y.val ≤ j.2.toNat := by omega
      have hy2 : j.1.toNat ≤ y.val := by omega
      have hlo : i.1 * 2 ^ j.1.toNat ≤ ((x.val : Nat) : Int) * 2 ^ y.val :=
        mul_two_pow_le hi0 hx.1 hy2
      have hhi : ((x.val : Nat) : Int) * 2 ^ y.val ≤ i.2 * 2 ^ j.2.toNat :=
        mul_two_pow_le (by omega) hx.2 hy1
      split_ifs with hs
      · have hlt : x.val * 2 ^ y.val < 2 ^ ty.numBits := by
          have : ((x.val * 2 ^ y.val : Nat) : Int) < 2 ^ ty.numBits := by
            push_cast
            omega
          exact_mod_cast this
        have hzv' : z.val = x.val * 2 ^ y.val := by
          rw [hzv, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt]
        unfold Iv.Has
        rw [hzv']
        push_cast
        omega
      · unfold Iv.Has
        omega
    · cases h
  | rotr =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer] at h
    split at h
    · rename_i hj32
      simp only [Option.some.injEq] at h
      subst h
      have hy32 : y.val < 2 ^ UScalarTy.U32.numBits := by
        have : ((y.val : Nat) : Int) < 2 ^ 32 := by omega
        simp only [UScalarTy.U32_numBits_eq]
        exact_mod_cast this
      refine ⟨UScalar.rotate_right x (UScalar.ofNatCore (ty := .U32) y.val hy32), ?_, ?_⟩
      · simp only [aeWordOpW, WordOp.aen, hy32, ↓reduceDIte]
        rfl
      · have hz : ((((UScalar.rotate_right x
            (UScalar.ofNatCore (ty := .U32) y.val hy32)).val : Nat) : Int)) <
            2 ^ ty.numBits := by
          exact_mod_cast (UScalar.rotate_right x _).hBounds
        unfold Iv.Has
        omega
    · cases h
  | rotl =>
    have hb : b = ty.numBits := by simpa [AeWordOp.atSize] using hbo
    subst hb
    simp only [wordXfer] at h
    split at h
    · rename_i hj32
      simp only [Option.some.injEq] at h
      subst h
      have hy32 : y.val < 2 ^ UScalarTy.U32.numBits := by
        have : ((y.val : Nat) : Int) < 2 ^ 32 := by omega
        simp only [UScalarTy.U32_numBits_eq]
        exact_mod_cast this
      refine ⟨UScalar.rotate_left x (UScalar.ofNatCore (ty := .U32) y.val hy32), ?_, ?_⟩
      · simp only [aeWordOpW, WordOp.aen, hy32, ↓reduceDIte]
        rfl
      · have hz : ((((UScalar.rotate_left x
            (UScalar.ofNatCore (ty := .U32) y.val hy32)).val : Nat) : Int)) <
            2 ^ ty.numBits := by
          exact_mod_cast (UScalar.rotate_left x _).hBounds
        unfold Iv.Has
        omega
    · cases h

theorem add_ok {ty : UScalarTy} (x y : UScalar ty) (h : x.val + y.val < 2 ^ ty.numBits) :
    ∃ z : UScalar ty, UScalar.add x y = .ok z ∧ z.val = x.val + y.val := by
  have he := UScalar.add_equiv x y
  rw [show (x + y : RustM (UScalar ty)) = UScalar.add x y from rfl] at he
  rcases hxy : UScalar.add x y with z | e | _ <;> rw [hxy] at he
  · exact ⟨z, rfl, he.2.1⟩
  · grind
  · exact he.elim

theorem sub_ok {ty : UScalarTy} (x y : UScalar ty) (h : y.val ≤ x.val) :
    ∃ z : UScalar ty, UScalar.sub x y = .ok z ∧ z.val = x.val - y.val := by
  have he := UScalar.sub_equiv x y
  rw [show (x - y : RustM (UScalar ty)) = UScalar.sub x y from rfl] at he
  rcases hxy : UScalar.sub x y with z | e | _ <;> rw [hxy] at he
  · exact ⟨z, rfl, by omega⟩
  · omega
  · exact he.elim

theorem mul_ok {ty : UScalarTy} (x y : UScalar ty) (h : x.val * y.val < 2 ^ ty.numBits) :
    ∃ z : UScalar ty, UScalar.mul x y = .ok z ∧ z.val = x.val * y.val := by
  have he := UScalar.mul_equiv x y
  rcases hxy : UScalar.mul x y with z | e | _ <;> rw [hxy] at he
  · exact ⟨z, rfl, he.2.1⟩
  · grind [UScalar.max]
  · exact he.elim

/-- The interval `checkedXfer` gives a checked operation at a width `b` at most the width of
    the Aeneas words holds the value of the Aeneas checked operation, which does not fail. -/
theorem checkedXfer_sound {ty : UScalarTy} {o : AeChecked} {b : Nat} (hble : b ≤ ty.numBits)
    {i j I : Iv} (hj0 : 0 ≤ j.1) (x y : UScalar ty) (hx : i.Has x.val)
    (hy : j.Has y.val) (h : checkedXfer o b i j = some I) :
    ∃ z, (aeCheckedA o).aen x y = .ok z ∧ I.Has z.val := by
  have hbb : (2 : Int) ^ b ≤ 2 ^ ty.numBits := pow_le_pow_right₀ (by norm_num) hble
  unfold Iv.Has at hx hy
  cases o with
  | add =>
    simp only [checkedXfer, ivAddZ] at h
    by_cases hs : i.2 + j.2 < 2 ^ b <;> simp only [hs, ite_true, ite_false] at h
    · simp only [Option.some.injEq] at h
      subst h
      have hm : x.val + y.val < 2 ^ ty.numBits := by
        have : ((x.val + y.val : Nat) : Int) < 2 ^ ty.numBits := by
          push_cast
          omega
        exact_mod_cast this
      obtain ⟨z, hz, hzv⟩ := add_ok x y hm
      refine ⟨z, hz, ?_⟩
      unfold Iv.Has
      rw [hzv]
      push_cast
      omega
    · cases h
  | sub =>
    simp only [checkedXfer, ivSubZ] at h
    by_cases hs : 0 ≤ i.1 - j.2 <;> simp only [hs, ite_true, ite_false] at h
    · simp only [Option.some.injEq] at h
      subst h
      have hle : y.val ≤ x.val := by
        have : ((y.val : Nat) : Int) ≤ x.val := by omega
        exact_mod_cast this
      obtain ⟨z, hz, hzv⟩ := sub_ok x y hle
      refine ⟨z, hz, ?_⟩
      unfold Iv.Has
      rw [hzv]
      push_cast [hle]
      omega
    · cases h
  | mul =>
    simp only [checkedXfer] at h
    by_cases hs : i.2 * j.2 < 2 ^ b <;> simp only [hs, ite_true, ite_false] at h
    · simp only [Option.some.injEq] at h
      subst h
      have hlo : i.1 * j.1 ≤ ((x.val : Nat) : Int) * ((y.val : Nat) : Int) :=
        mul_le_mul hx.1 hy.1 hj0 (by omega)
      have hhi : ((x.val : Nat) : Int) * ((y.val : Nat) : Int) ≤ i.2 * j.2 :=
        mul_le_mul hx.2 hy.2 (by omega) (by omega)
      have hm : x.val * y.val < 2 ^ ty.numBits := by
        have : ((x.val * y.val : Nat) : Int) < 2 ^ ty.numBits := by
          push_cast
          omega
        exact_mod_cast this
      obtain ⟨z, hz, hzv⟩ := mul_ok x y hm
      refine ⟨z, hz, ?_⟩
      unfold Iv.Has
      rw [hzv]
      push_cast
      omega
    · cases h

/-! ## The unary names -/

theorem aeTagAt?_spec {pre f : String} {b : Nat} (h : aeTagAt? pre f = some b) :
    ∃ ty, f = pre ++ uTag ty ∧ tableTy ty = true ∧ ty.numBits = b := by
  obtain ⟨⟨tag, b'⟩, ht, h1⟩ := List.exists_of_findSome?_eq_some h
  simp only [aeTags, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at ht
  clear h
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨.U8, ?_⟩
    split at h1
    simp_all [uTag, tableTy]
  · refine ⟨.U16, ?_⟩
    split at h1
    simp_all [uTag, tableTy]
  · refine ⟨.U32, ?_⟩
    split at h1
    simp_all [uTag, tableTy]
  · refine ⟨.U64, ?_⟩
    split at h1
    simp_all [uTag, tableTy]
  · split at h1
    simp_all

theorem aeCall1_notName {ty : UScalarTy} (hty : tableTy ty = true) (a : Value) :
    aeCall1 ("Not#" ++ uTag ty) a = (readW ty a >>= fun x => .ok (wordV (~~~x))) := by
  have h1 : ¬ ("Not#" ++ uTag ty = "Not") := by cases ty <;> decide +kernel
  have h2 : tagTyAt? "Not#" ("Not#" ++ uTag ty) = some ty := by cases ty <;> decide +kernel
  unfold aeCall1
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), h2]
  simp only [hty, ite_true]

theorem aeCall1_castName {ty : UScalarTy} (hty : tableTy ty = true) (a : Value) :
    aeCall1 ("cast#" ++ uTag ty) a =
      (readW .U64 a >>= fun x => .ok (wordV (UScalar.cast ty x))) := by
  have h1 : ¬ ("cast#" ++ uTag ty = "Not") := by cases ty <;> decide +kernel
  have h2 : tagTyAt? "Not#" ("cast#" ++ uTag ty) = none := by cases ty <;> decide +kernel
  have h3 : tagTyAt? "cast#" ("cast#" ++ uTag ty) = some ty := by cases ty <;> decide +kernel
  unfold aeCall1
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), h2, h3]
  simp only [hty, ite_true]

/-- A unary call accepted by `aeXfer1` reads to a value that its abstract result holds of. -/
theorem aeXfer1_sound {f : String} {r t : NfTy} {x : AVal t} {a : AVal r} {xv : t.denote}
    (h : aeXfer1 f r t x = some a) (hx : AVal.Mem t x xv) :
    ∃ v y, aeCall1 f (enc t xv) = .ok v ∧ dec r v = some y ∧ AVal.Mem r a y := by
  unfold aeXfer1 at h
  by_cases hf : f = "Not"
  · subst hf
    simp only at h
    rcases hp : bitArg t x with _ | p
    · simp [hp] at h
    have hr : retBit r p.not = some a := by simpa [hp] using h
    obtain ⟨bv, he, hbv⟩ := bitArg_spec hp hx
    have hnot : p.not.val = none ∨ p.not.val = some !bv := by
      rcases hbv with hb | hb <;> simp [ABit.not, hb]
    obtain ⟨y, hy, hym⟩ := retBit_spec hr hnot
    refine ⟨.bool !bv, y, ?_, hy, hym⟩
    rw [he]
    rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hf)] at h
    rcases hn : aeTagAt? "Not#" f with _ | b
    · rcases hc : aeTagAt? "cast#" f with _ | b
      · simp only [hn, hc] at h
        cases h
      · simp only [hn, hc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨i, hi, h⟩ := h
        split at h
        · rename_i hb
          obtain ⟨ty, rfl, hty, rfl⟩ := aeTagAt?_spec hc
          obtain ⟨n, he, hn'⟩ := wordArg_spec hi hx
          obtain ⟨u, hu, huv⟩ := readW_nat (ty := .U64) (lt_of_below hb hn')
          have hcv : (UScalar.cast ty u).val = n % 2 ^ ty.numBits := by
            rw [UScalar.cast_val_eq, huv]
          have hmod := Nat.mod_lt n (Nat.two_pow_pos ty.numBits)
          have hhas : (if i.2 < 2 ^ ty.numBits then i else ((0, 2 ^ ty.numBits - 1) : Iv)).Has
              (UScalar.cast ty u).val := by
            rw [hcv]
            unfold Iv.Has at hn' ⊢
            by_cases hs : i.2 < 2 ^ ty.numBits
            · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
              have hlt : n < 2 ^ ty.numBits := by
                have : (n : Int) < 2 ^ ty.numBits := lt_of_le_of_lt hn'.2 hs
                exact_mod_cast this
              rw [Nat.mod_eq_of_lt hlt]
              exact hn'
            · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
              have : ((n % 2 ^ ty.numBits : Nat) : Int) < 2 ^ ty.numBits := by
                exact_mod_cast hmod
              omega
          obtain ⟨y, hy, hym⟩ := retWord_spec h hhas
          refine ⟨wordV (UScalar.cast ty u), y, ?_, hy, hym⟩
          rw [he, aeCall1_castName hty, hu]
          rfl
        · cases h
    · simp only [hn, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨i, hi, h⟩ := h
      split at h
      · rename_i hb
        obtain ⟨ty, rfl, hty, rfl⟩ := aeTagAt?_spec hn
        obtain ⟨n, he, hn'⟩ := wordArg_spec hi hx
        have hnb := lt_of_below hb hn'
        obtain ⟨u, hu, huv⟩ := readW_nat (ty := ty) hnb
        have hnv : (~~~u).val = 2 ^ ty.numBits - 1 - n := by
          rw [← huv]
          change (~~~u.bv).toNat = _
          rw [BitVec.toNat_not]
          rfl
        have hhas : Iv.Has (2 ^ ty.numBits - 1 - (nn i).2, 2 ^ ty.numBits - 1 - (nn i).1)
            (~~~u).val := by
          have hnn := has_nn hn'
          rw [hnv]
          unfold Iv.Has at hnn ⊢
          have : ((n : Nat) : Int) < 2 ^ ty.numBits := by exact_mod_cast hnb
          push_cast [show n ≤ 2 ^ ty.numBits - 1 by omega, Nat.one_le_two_pow]
          omega
        obtain ⟨y, hy, hym⟩ := retWord_spec h hhas
        refine ⟨wordV (~~~u), y, ?_, hy, hym⟩
        rw [he, aeCall1_notName hty, hu]
        rfl
      · cases h

/-! ## The binary names -/

theorem aeCheckedName?_spec {f : String} {o : AeChecked} {b : Nat}
    (h : aeCheckedName? f = some (o, b)) :
    ∃ ty, f = checkedName (aeCheckedA o) ty ∧ checkedTy ty = true ∧ b ≤ ty.numBits := by
  have hU := usize_ge_32
  obtain ⟨⟨tag, b'⟩, ht, h1⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨⟨pre, o'⟩, ho, h2⟩ := List.exists_of_findSome?_eq_some h1
  simp only [aeTags, List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at ht ho
  simp only at h2
  clear h h1
  rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨.U8, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [checkedName, uTag, checkedTy, tableTy, aeCheckedA]
  · refine ⟨.U16, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [checkedName, uTag, checkedTy, tableTy, aeCheckedA]
  · refine ⟨.U32, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [checkedName, uTag, checkedTy, tableTy, aeCheckedA]
  · refine ⟨.U64, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [checkedName, uTag, checkedTy, tableTy, aeCheckedA]
  · refine ⟨.Usize, ?_⟩
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    (split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h2) <;>
    obtain ⟨rfl, rfl⟩ := h2 <;> simp_all [checkedName, uTag, checkedTy, tableTy, aeCheckedA]

theorem aeCmp?_cases {f : String} {p : NfPred} (h : aeCmp? f = some p) :
    (p = .ult ∧ f = CmpOp.lt.name) ∨ (p = .ule ∧ f = CmpOp.le.name) ∨
      (p = .ugt ∧ f = CmpOp.gt.name) ∨ (p = .uge ∧ f = CmpOp.ge.name) ∨
      (p = .eq ∧ f = CmpOp.eq.name) ∨ (p = .ne ∧ f = CmpOp.ne.name) := by
  unfold aeCmp? at h
  split at h <;> simp_all [CmpOp.name]

theorem aeConn?_cases {f : String} {k : Conn} (h : aeConn? f = some k) :
    (k = .and ∧ f = BoolOp.and.name) ∨ (k = .or ∧ f = BoolOp.or.name) ∨
      (k = .not ∧ f = "Not") := by
  unfold aeConn? at h
  split at h <;> simp_all [BoolOp.name]

theorem abit_and_mem {p q : ABit} {b1 b2 : Bool} (h1 : p.val = none ∨ p.val = some b1)
    (h2 : q.val = none ∨ q.val = some b2) :
    (p.and q).val = none ∨ (p.and q).val = some (b1 && b2) := by
  unfold ABit.and
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp only [h1, h2] <;>
    cases b1 <;> cases b2 <;> simp

theorem abit_or_mem {p q : ABit} {b1 b2 : Bool} (h1 : p.val = none ∨ p.val = some b1)
    (h2 : q.val = none ∨ q.val = some b2) :
    (p.or q).val = none ∨ (p.or q).val = some (b1 || b2) := by
  unfold ABit.or
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp only [h1, h2] <;>
    cases b1 <;> cases b2 <;> simp

/-- The comparison `c` of two words is the comparison `p` of the words of the same values. -/
theorem cmp_aen_denote {p : NfPred} {c : CmpOp}
    (hpc : (p = .ult ∧ c = .lt) ∨ (p = .ule ∧ c = .le) ∨ (p = .ugt ∧ c = .gt) ∨
      (p = .uge ∧ c = .ge) ∨ (p = .eq ∧ c = .eq) ∨ (p = .ne ∧ c = .ne))
    {w : Nat} (u v : U64) (x y : BitVec w) (hu : u.val = x.toNat) (hv : v.val = y.toNat) :
    c.aen u v = p.denote x y := by
  rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [CmpOp.aen, NfPred.denote, hu, hv, BitVec.ult, BitVec.ule, BitVec.toNat_inj]

/-- The value `cmpVal` gives a comparison, when it gives one, is the comparison of words in
    the intervals. -/
theorem cmpVal_sound {p : NfPred} {c : CmpOp}
    (hpc : (p = .ult ∧ c = .lt) ∨ (p = .ule ∧ c = .le) ∨ (p = .ugt ∧ c = .gt) ∨
      (p = .uge ∧ c = .ge) ∨ (p = .eq ∧ c = .eq) ∨ (p = .ne ∧ c = .ne))
    {i j : Iv} (u v : U64) (hu : i.Has u.val) (hv : j.Has v.val) :
    cmpVal p i j = none ∨ cmpVal p i j = some (c.aen u v) := by
  unfold Iv.Has at hu hv
  rcases hpc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [cmpVal, CmpOp.aen] <;> split_ifs <;> simp <;> omega

theorem readArr_nats (ns : List Nat) (h64 : ∀ k ∈ ns, k < 2 ^ 64) (hlen : ns.length < 2 ^ 32) :
    ∃ arr : (Σ n : Usize, HaxLean.Aeneas.Std.Array U64 n),
      readArr (.array (ns.map fun (k : Nat) => Value.int (k : Int))) = .ok arr ∧
      arr.2.val.map UScalar.val = ns := by
  obtain ⟨us, hus, husv⟩ := readWs_nats ns h64
  have hl : us.length = ns.length := by rw [← husv, List.length_map]
  have hlen' : us.length < 2 ^ UScalarTy.Usize.numBits := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) usize_ge_32
    omega
  obtain ⟨nU, hnU, hnUv⟩ := readW_nat (ty := .Usize) hlen'
  have hd : us.length = nU.val := hnUv.symm
  refine ⟨⟨nU, HaxLean.Aeneas.Std.Array.make nU us hd⟩, ?_, husv⟩
  rw [readArr, hus, bind_tc_ok, show litA .Usize (us.length : Int) = .ok nU from hnU,
    bind_tc_ok, dite_eq_left_of_eq_true (eq_true hd)]

/-- A binary call accepted by `aeXfer2` reads to a value that its abstract result holds of. -/
theorem aeXfer2_sound {f : String} {r t c : NfTy} {x : AVal t} {y : AVal c} {a : AVal r}
    {xv : t.denote} {yv : c.denote} (h : aeXfer2 f r t c x y = some a)
    (hx : AVal.Mem t x xv) (hy : AVal.Mem c y yv) :
    ∃ v z, aeCall2 f (enc t xv) (enc c yv) = .ok v ∧ dec r v = some z ∧ AVal.Mem r a z := by
  unfold aeXfer2 at h
  rcases hw : aeWordName? f with _ | ⟨o, b⟩
  · rcases hc : aeCheckedName? f with _ | ⟨o, b⟩
    · rcases hp : aeCmp? f with _ | p
      · rcases hk : aeConn? f with _ | k
        · by_cases hf : f = "index"
          · subst hf
            simp only [hw, hc, hp, hk, ite_true, Option.bind_eq_bind,
              Option.bind_eq_some_iff] at h
            obtain ⟨⟨n, e⟩, ha, h⟩ := h
            simp only at h
            obtain ⟨i, hi, h⟩ := h
            by_cases hb : (below 64 e && decide (n < 2 ^ 32) && below 32 i &&
                decide (i.2 < (n : Int))) = true
            · simp only [hb, ite_true] at h
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
              obtain ⟨⟨⟨hbe, hn32⟩, hbi⟩, hin⟩ := hb
              obtain ⟨ns, hens, hlen, hns⟩ := arrArg_spec ha hx
              obtain ⟨m, hem, hm⟩ := wordArg_spec hi hy
              obtain ⟨arr, harr, harrv⟩ :=
                readArr_nats ns (fun k hk => lt_of_below hbe (hns k hk)) (by omega)
              have hm32 := lt_of_below hbi hm
              obtain ⟨iU, hiU, hiUv⟩ := readW_nat (ty := .Usize)
                (lt_of_lt_of_le hm32 (Nat.pow_le_pow_right (by norm_num) usize_ge_32))
              have hmn : m < ns.length := by
                have : (m : Int) < n := lt_of_le_of_lt hm.2 hin
                omega
              have hbound : iU.val < arr.2.length := by
                have := congrArg List.length harrv
                simp only [List.length_map] at this
                simp only [HaxLean.Aeneas.Std.Array.length]
                omega
              have hz : arr.2.index_usize iU = .ok (arr.2.val[iU.val]'hbound) := by
                simp [HaxLean.Aeneas.Std.Array.index_usize, hbound]
              have hzmem : arr.2.val[iU.val]'hbound ∈ arr.2.val := List.getElem_mem hbound
              generalize arr.2.val[iU.val]'hbound = z at hz hzmem
              have hzns : z.val ∈ ns := harrv ▸ List.mem_map_of_mem hzmem
              obtain ⟨w, hwd, hwm⟩ := retWord_spec h (hns _ hzns)
              refine ⟨wordV z, w, ?_, hwd, hwm⟩
              rw [hens, hem, aeCall2_index, harr, bind_tc_ok, hiU, bind_tc_ok, hz, bind_tc_ok]
            · rw [Bool.not_eq_true] at hb
              simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq] at h
          · simp [hw, hc, hp, hk, hf] at h
        · rcases aeConn?_cases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · simp only [hw, hc, hp, hk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨p1, hp1, p2, hp2, hr⟩ := h
            obtain ⟨b1, he1, hb1⟩ := bitArg_spec hp1 hx
            obtain ⟨b2, he2, hb2⟩ := bitArg_spec hp2 hy
            obtain ⟨z, hz, hzm⟩ := retBit_spec hr (abit_and_mem hb1 hb2)
            refine ⟨.bool (b1 && b2), z, ?_, hz, hzm⟩
            rw [he1, he2, aeCall2_boolName]
            rfl
          · simp only [hw, hc, hp, hk, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
            obtain ⟨p1, hp1, p2, hp2, hr⟩ := h
            obtain ⟨b1, he1, hb1⟩ := bitArg_spec hp1 hx
            obtain ⟨b2, he2, hb2⟩ := bitArg_spec hp2 hy
            obtain ⟨z, hz, hzm⟩ := retBit_spec hr (abit_or_mem hb1 hb2)
            refine ⟨.bool (b1 || b2), z, ?_, hz, hzm⟩
            rw [he1, he2, aeCall2_boolName]
            rfl
          · simp [hw, hc, hp, hk] at h
      · simp only [hw, hc, hp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨i, hi, j, hj, h⟩ := h
        by_cases hb : (below 64 i && below 64 j) = true
        · simp only [hb, ite_true] at h
          simp only [Bool.and_eq_true] at hb
          obtain ⟨n, hen, hn⟩ := wordArg_spec hi hx
          obtain ⟨m, hem, hm⟩ := wordArg_spec hj hy
          obtain ⟨u, hu, huv⟩ := readW_nat (ty := .U64) (lt_of_below hb.1 hn)
          obtain ⟨u', hu', huv'⟩ := readW_nat (ty := .U64) (lt_of_below hb.2 hm)
          obtain ⟨c, hpc, rfl⟩ : ∃ c : CmpOp, ((p = .ult ∧ c = .lt) ∨ (p = .ule ∧ c = .le) ∨
              (p = .ugt ∧ c = .gt) ∨ (p = .uge ∧ c = .ge) ∨ (p = .eq ∧ c = .eq) ∨
              (p = .ne ∧ c = .ne)) ∧ f = c.name := by
            rcases aeCmp?_cases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
              ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨.lt, by simp, rfl⟩
            · exact ⟨.le, by simp, rfl⟩
            · exact ⟨.gt, by simp, rfl⟩
            · exact ⟨.ge, by simp, rfl⟩
            · exact ⟨.eq, by simp, rfl⟩
            · exact ⟨.ne, by simp, rfl⟩
          have hcv := cmpVal_sound hpc u u' (i := nn i) (j := nn j)
            (by rw [huv]; exact has_nn hn) (by rw [huv']; exact has_nn hm)
          obtain ⟨z, hz, hzm⟩ := retBit_spec h (b := c.aen u u') (by simpa using hcv)
          refine ⟨.bool (c.aen u u'), z, ?_, hz, hzm⟩
          rw [hen, hem, aeCall2_cmpName, hu, hu', bind_tc_ok, bind_tc_ok]
        · simp [hb] at h
    · simp only [hw, hc, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, rfl, hty, hble⟩ := aeCheckedName?_spec hc
      obtain ⟨i, hi, j, hj, h⟩ := h
      by_cases hb : (below b i && below b j) = true
      · simp only [hb, ite_true] at h
        simp only [Bool.and_eq_true] at hb
        obtain ⟨I, hI, hr⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨n, hen, hn⟩ := wordArg_spec hi hx
        obtain ⟨m, hem, hm⟩ := wordArg_spec hj hy
        have hnb := lt_of_below hb.1 hn
        have hmb := lt_of_below hb.2 hm
        have hbb : 2 ^ b ≤ 2 ^ ty.numBits := Nat.pow_le_pow_right (by norm_num) hble
        obtain ⟨u, hu, huv⟩ := readW_nat (ty := ty) (lt_of_lt_of_le hnb hbb)
        obtain ⟨u', hu', huv'⟩ := readW_nat (ty := ty) (lt_of_lt_of_le hmb hbb)
        obtain ⟨z, hz, hzI⟩ := checkedXfer_sound hble (nn_fst j) u u'
          (by rw [huv]; exact has_nn hn) (by rw [huv']; exact has_nn hm) hI
        obtain ⟨w, hwd, hwm⟩ := retWord_spec hr hzI
        refine ⟨wordV z, w, ?_, hwd, hwm⟩
        rw [hen, hem, aeCall2_checkedName hty _ (by cases o <;> rfl), hu, hu', bind_tc_ok,
          bind_tc_ok, hz, bind_tc_ok]
      · simp [hb] at h
  · simp only [hw, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨ty, rfl, hwa, hble, hbo⟩ := aeWordName?_spec hw
    obtain ⟨i, hi, j, hj, h⟩ := h
    by_cases hb : (below b i && below b j) = true
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] at h
      simp only [Bool.and_eq_true] at hb
      obtain ⟨I, hI, hr⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨n, hen, hn⟩ := wordArg_spec hi hx
      obtain ⟨m, hem, hm⟩ := wordArg_spec hj hy
      have hnb := lt_of_below hb.1 hn
      have hmb := lt_of_below hb.2 hm
      have hbb : 2 ^ b ≤ 2 ^ ty.numBits := Nat.pow_le_pow_right (by norm_num) hble
      obtain ⟨u, hu, huv⟩ := readW_nat (ty := ty) (lt_of_lt_of_le hnb hbb)
      obtain ⟨u', hu', huv'⟩ := readW_nat (ty := ty) (lt_of_lt_of_le hmb hbb)
      obtain ⟨z, hz, hzI⟩ := wordXfer_sound hble hbo (nn_fst i) (nn_fst j) u u'
        (by rw [huv]; exact has_nn hn) (by rw [huv']; exact has_nn hm) (by rw [huv]; exact hnb)
        (by rw [huv']; exact hmb) hI
      obtain ⟨w, hwd, hwm⟩ := retWord_spec hr hzI
      refine ⟨wordV z, w, ?_, hwd, hwm⟩
      rw [hen, hem, aeCall2_opName hwa, hu, hu']
      change ((aeWordOpW o).aen u u' >>= fun z => RustM.ok (wordV z)) = _
      rw [hz]
      rfl
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)] at h
      cases h

/-! ## The ternary names -/

theorem retArr_spec {r : NfTy} {n : Nat} {I : Iv} {a : AVal r} (h : retArr r n I = some a)
    (zs : List Nat) (hlen : zs.length = n) (hz : ∀ k ∈ zs, I.Has k) :
    ∃ y, dec r (.array (zs.map fun (k : Nat) => Value.int (k : Int))) = some y ∧
      AVal.Mem r a y := by
  cases r with
  | arr m s =>
    cases s with
    | word w =>
      simp only [retArr] at h
      by_cases hc : (decide (m = n) && below w I) = true
      · simp only [hc, ite_true, Option.some.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨rfl, hb⟩ := hc
        subst h
        obtain ⟨ys, hys, hysv⟩ :=
          mapM_dec_word (w := w) zs (fun k hk => lt_of_below hb (hz k hk))
        have hyl : ys.length = zs.length := by rw [← hysv, List.length_map]
        refine ⟨fun i => ys[i.1]'(by omega), ?_, ?_⟩
        · simp [dec, hys, hyl, hlen]
        · intro j
          apply hz
          grind
      · rw [Bool.not_eq_true] at hc
        simp only [hc, Bool.false_eq_true, ite_false, reduceCtorEq] at h
    | _ => simp [retArr] at h
  | _ => simp [retArr] at h

theorem aeCall3_update (a i v : Value) :
    aeCall3 "array_update" a i v =
      (readArr a >>= fun arr => readW .Usize i >>= fun j => readW .U64 v >>= fun x =>
        arr.2.update j x >>= fun arr' => .ok (arrV arr')) := by
  unfold aeCall3
  simp

theorem aeCall3_select (a i v : Value) :
    aeCall3 "select" a i v =
      (readB a >>= fun k => readW .U64 i >>= fun x => readW .U64 v >>= fun y =>
        .ok (wordV (selW k x y))) := by
  unfold aeCall3
  simp

/-- A ternary call accepted by `aeXfer3` reads to a value that its abstract result holds of. -/
theorem aeXfer3_sound {f : String} {r t c d : NfTy} {x : AVal t} {y : AVal c} {z : AVal d}
    {a : AVal r} {xv : t.denote} {yv : c.denote} {zv : d.denote}
    (h : aeXfer3 f r t c d x y z = some a) (hx : AVal.Mem t x xv) (hy : AVal.Mem c y yv)
    (hz : AVal.Mem d z zv) :
    ∃ v w, aeCall3 f (enc t xv) (enc c yv) (enc d zv) = .ok v ∧ dec r v = some w ∧
      AVal.Mem r a w := by
  unfold aeXfer3 at h
  by_cases hf : f = "array_update"
  · subst hf
    simp only [ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨n, e⟩, ha, h⟩ := h
    simp only at h
    obtain ⟨i, hi, vI, hv, h⟩ := h
    by_cases hb : (below 64 e && decide (n < 2 ^ 32) && below 32 i && decide (i.2 < (n : Int)) &&
        below 64 vI) = true
    · simp only [hb, ite_true] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨⟨⟨hbe, hn32⟩, hbi⟩, hin⟩, hbv⟩ := hb
      obtain ⟨ns, hens, hlen, hns⟩ := arrArg_spec ha hx
      obtain ⟨m, hem, hm⟩ := wordArg_spec hi hy
      obtain ⟨k, hek, hk⟩ := wordArg_spec hv hz
      obtain ⟨arr, harr, harrv⟩ :=
        readArr_nats ns (fun k hk => lt_of_below hbe (hns k hk)) (by omega)
      have hm32 := lt_of_below hbi hm
      obtain ⟨iU, hiU, hiUv⟩ := readW_nat (ty := .Usize)
        (lt_of_lt_of_le hm32 (Nat.pow_le_pow_right (by norm_num) usize_ge_32))
      obtain ⟨u, hu, huv⟩ := readW_nat (ty := .U64) (lt_of_below hbv hk)
      have hal : arr.2.val.length = ns.length := by
        have := congrArg List.length harrv
        grind
      have hbound : iU.val < arr.2.length := by
        have : (m : Int) < n := lt_of_le_of_lt hm.2 hin
        simp only [HaxLean.Aeneas.Std.Array.length]
        omega
      obtain ⟨arr', hupd, harr'⟩ : ∃ arr' : HaxLean.Aeneas.Std.Array U64 arr.1,
          arr.2.update iU u = .ok arr' ∧ arr'.val = arr.2.val.set iU.val u :=
        ⟨⟨arr.2.val.set iU.val u, by simp [arr.2.property]⟩,
          by simp [HaxLean.Aeneas.Std.Array.update, hbound], rfl⟩
      have hzlen : (arr'.val.map UScalar.val).length = n := by
        simp [harr', hal, hlen]
      have hzin : ∀ q ∈ arr'.val.map UScalar.val, (ivHull e vI).Has q := by
        intro q hq
        rw [harr'] at hq
        simp only [List.mem_map] at hq
        obtain ⟨w, hw, rfl⟩ := hq
        rcases List.mem_or_eq_of_mem_set hw with hw | rfl
        · have := hns _ (harrv ▸ List.mem_map_of_mem hw)
          unfold Iv.Has ivHull at *
          omega
        · rw [huv]
          unfold Iv.Has ivHull at *
          omega
      obtain ⟨w, hwd, hwm⟩ := retArr_spec h _ hzlen hzin
      refine ⟨arrV arr', w, ?_, ?_, hwm⟩
      · rw [hens, hem, hek, aeCall3_update, harr, bind_tc_ok, hiU, bind_tc_ok, hu, bind_tc_ok,
          hupd, bind_tc_ok]
      · have hav : arrV arr' =
            .array ((arr'.val.map UScalar.val).map fun (k : Nat) => Value.int (k : Int)) := by
          simp [arrV, wordV, List.map_map, Function.comp_def]
        rw [hav]
        exact hwd
    · rw [Bool.not_eq_true] at hb
      simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq] at h
  · simp only [hf, ite_false] at h
    by_cases hs : f = "select"
    · subst hs
      simp only [ite_true, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨p, hp, i, hi, j, hj, h⟩ := h
      by_cases hb : (below 64 i && below 64 j) = true
      · simp only [hb, ite_true] at h
        simp only [Bool.and_eq_true] at hb
        obtain ⟨kb, hek, hkb⟩ := bitArg_spec hp hx
        obtain ⟨n, hen, hn⟩ := wordArg_spec hi hy
        obtain ⟨m, hem, hm⟩ := wordArg_spec hj hz
        obtain ⟨u, hu, huv⟩ := readW_nat (ty := .U64) (lt_of_below hb.1 hn)
        obtain ⟨u', hu', huv'⟩ := readW_nat (ty := .U64) (lt_of_below hb.2 hm)
        have hsel : Iv.Has (match p.val with
            | some true => i
            | some false => j
            | none => ivHull i j) (selW kb u u').val := by
          unfold Iv.Has ivHull at *
          rcases hkb with hk | hk <;> rw [hk] <;> cases kb <;> simp [selW, huv, huv'] <;> omega
        obtain ⟨w, hwd, hwm⟩ := retWord_spec h hsel
        refine ⟨wordV (selW kb u u'), w, ?_, hwd, hwm⟩
        rw [hek, hen, hem, aeCall3_select]
        rw [show readB (Value.bool kb) = .ok kb from rfl, bind_tc_ok, hu, bind_tc_ok, hu',
          bind_tc_ok]
      · rw [Bool.not_eq_true] at hb
        simp only [hb, Bool.false_eq_true, ite_false, reduceCtorEq] at h
    · simp only [hs, ite_false, reduceCtorEq] at h

/-! ## The specification -/

/-- A call accepted by `aeXfer` has a value of `aeTable` that its abstract result holds of. -/
theorem aeXfer_sound (f : String) (as : List NfTy) (r : NfTy) (avs : AVals as) (a : AVal r)
    (xs : HVector NfTy.denote as) (h : aeXfer f as r avs = some a) (hm : AVals.Mem avs xs) :
    ∃ y, aeTable.call f as r xs = some y ∧ AVal.Mem r a y := by
  match as, avs, xs, h, hm with
  | [t], .cons x .nil, .cons xv .nil, h, hm =>
    obtain ⟨v, y, hv, hy, hym⟩ := aeXfer1_sound h hm.1
    exact ⟨y, by rw [aeTable_call_of_ok (f := f) (as := [t]) (xs := .cons xv .nil) hv]; exact hy,
      hym⟩
  | [t, c], .cons x (.cons y .nil), .cons xv (.cons yv .nil), h, hm =>
    obtain ⟨v, z, hv, hz, hzm⟩ := aeXfer2_sound h hm.1 hm.2.1
    exact ⟨z, by
      rw [aeTable_call_of_ok (f := f) (as := [t, c]) (xs := .cons xv (.cons yv .nil)) hv]
      exact hz, hzm⟩
  | [t, c, d], .cons x (.cons y (.cons z .nil)), .cons xv (.cons yv (.cons zv .nil)), h, hm =>
    obtain ⟨v, w, hv, hw, hwm⟩ := aeXfer3_sound h hm.1 hm.2.1 hm.2.2.1
    exact ⟨w, by
      rw [aeTable_call_of_ok (f := f) (as := [t, c, d])
        (xs := .cons xv (.cons yv (.cons zv .nil))) hv]
      exact hw, hwm⟩
  | [], .nil, .nil, h, _ => simp [aeXfer] at h
  | _ :: _ :: _ :: _ :: _, .cons _ (.cons _ (.cons _ (.cons _ _))), _, h, _ =>
    simp [aeXfer] at h

theorem readW_int_val {ty : UScalarTy} {n : Nat} {u : UScalar ty}
    (h : readW ty (.int (n : Int)) = .ok u) : u.val = n := by
  have := readW_ok h
  simp only [wordV, Value.int.injEq] at this
  omega

end RangeSpec

open RangeSpec in
/-- **The name specification of the Aeneas reading is sound for its leaf table.** A call that
    the transfer function `aeXfer` accepts on abstract arguments holding of the concrete
    arguments returns a value of `aeTable` in the abstract result; a comparison name of
    `aeCmp?` answers with its comparison and a connective name of `aeConn?` with its
    connective. -/
theorem aeSpec_sound : aeSpec.SoundAt aeTable where
  xfer := aeXfer_sound
  cmp := by
    intro f p w x y b hp hc
    obtain ⟨v, hv, hd⟩ := aeTable_call_ok hc
    obtain ⟨c, hpc, rfl⟩ : ∃ c : CmpOp, ((p = .ult ∧ c = .lt) ∨ (p = .ule ∧ c = .le) ∨
        (p = .ugt ∧ c = .gt) ∨ (p = .uge ∧ c = .ge) ∨ (p = .eq ∧ c = .eq) ∨
        (p = .ne ∧ c = .ne)) ∧ f = c.name := by
      rcases aeCmp?_cases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨.lt, by simp, rfl⟩
      · exact ⟨.le, by simp, rfl⟩
      · exact ⟨.gt, by simp, rfl⟩
      · exact ⟨.ge, by simp, rfl⟩
      · exact ⟨.eq, by simp, rfl⟩
      · exact ⟨.ne, by simp, rfl⟩
    change aeCall2 c.name (.int (x.toNat : Int)) (.int (y.toNat : Int)) = .ok v at hv
    rw [aeCall2_cmpName] at hv
    obtain ⟨u, hu, hv⟩ := rustM_bind_ok hv
    obtain ⟨u', hu', hv⟩ := rustM_bind_ok hv
    cases hv
    simp only [dec, Option.some.injEq] at hd
    rw [← hd]
    exact cmp_aen_denote hpc u u' x y (readW_int_val hu) (readW_int_val hu')
  and_ := by
    intro f x y b hk hc
    obtain ⟨v, hv, hd⟩ := aeTable_call_ok hc
    rcases aeConn?_cases hk with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · change aeCall2 BoolOp.and.name (.bool x) (.bool y) = .ok v at hv
      rw [aeCall2_boolName] at hv
      change RustM.ok (Value.bool (x && y)) = .ok v at hv
      cases hv
      simp only [dec, Option.some.injEq] at hd
      exact hd.symm
    · cases h
    · cases h
  or_ := by
    intro f x y b hk hc
    obtain ⟨v, hv, hd⟩ := aeTable_call_ok hc
    rcases aeConn?_cases hk with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩
    · cases h
    · change aeCall2 BoolOp.or.name (.bool x) (.bool y) = .ok v at hv
      rw [aeCall2_boolName] at hv
      change RustM.ok (Value.bool (x || y)) = .ok v at hv
      cases hv
      simp only [dec, Option.some.injEq] at hd
      exact hd.symm
    · cases h
  not_ := by
    intro f x b hk hc
    obtain ⟨v, hv, hd⟩ := aeTable_call_ok hc
    rcases aeConn?_cases hk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩
    · cases h
    · cases h
    · change aeCall1 "Not" (.bool x) = .ok v at hv
      unfold aeCall1 at hv
      simp only [ite_true] at hv
      change RustM.ok (Value.bool !x) = .ok v at hv
      cases hv
      simp only [dec, Option.some.injEq] at hd
      exact hd.symm

end CatCrypt.Crypto.SecureCompilation.AeneasFront
