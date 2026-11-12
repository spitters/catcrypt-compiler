/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront

/-!
# Compiled bytes of a reified function on scalars and word arrays

`leanFront_correct_mixed` states `leanFront_correct` for a layout without constants whose
parameters are `u64` scalars and word arrays in any order: each binding of the entry
environment is the parameter's name with the value its register denotes, the integer of the
register for a scalar and the words at the register's address for an array
(`AbiArg.read`). `AbiArg.read_eq_enc_zmod` and `AbiArg.read_eq_enc_words` give that value as
the encoding of a field element, respectively of an array.

The instance `mix_bytes` compiles a function over BabyBear that reads two arrays at fixed
indices and multiplies by a scalar, under the layout `mixAbi` with an array in `%rdi`, the
scalar in `%rsi` and an array in `%rdx`.

## Main results

* `hax64WExit_index_zmod` — the table `hax64WExit` at `index` on an encoded array of field
  elements and an index in range.
* `AbiArg.read_eq_enc_zmod`, `AbiArg.read_eq_enc_words` — the value a parameter denotes, as
  an encoding.
* `leanFront_correct_mixed` — the decoded bytes of `compileA` compute the function of an
  ascent result under a layout of scalars and word arrays.
* `mix_fnCorres` — the literal of `mixLean` denotes it under `hax64WExit`, for arrays of at
  least the read lengths.
* `mix_compileA_isSome` — `compileA` accepts the typed literal under `mixAbi`.
* `mix_bytes`, `mix_compileA_correct` — the compiled bytes of `mixLean` compute it on the
  arrays and the scalar the entry state holds.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open _root_.Hax (TExpr ImpExpr Value)
open _root_.Hax.Ascent (FnCorres HaxEnc enc bindParams)
open CatCrypt.Crypto.Hax (hax64WExit spineLamFree arrayOps_hax64WExit)
open CatCrypt.Hax.ReifyField (enc_zmod)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## The index leaf over a prime field -/

/-- **`index` under `hax64WExit` on field elements**: at a modulus below `2 ^ 64`, on the
    encoding of an array of elements of `ZMod p` and an index in range, the table answers the
    encoding of `Hax.index`. -/
theorem hax64WExit_index_zmod {p : ℕ} [NeZero p] (hp : p < 2 ^ 64) (a : Array (ZMod p))
    (i : Int) (h0 : 0 ≤ i) (h : i < (a.size : Int)) :
    hax64WExit "index" [enc a, .int i] = some (enc (_root_.Hax.index a i)) := by
  have hlt : i.toNat < a.size := by omega
  have hi : i.toNat < (a.toList.map enc).length := by simpa using hlt
  have hcf : ((a.toList.map enc)[i.toNat]).isControlFlow = false := by
    simp [enc_zmod hp, Value.isControlFlow]
  have hr := arrayOps_hax64WExit.index _ i.toNat hi hcf
  rw [Int.toNat_of_nonneg h0] at hr
  rw [show enc a = .array (a.toList.map enc) from rfl, hr]
  simp [_root_.Hax.index, hlt]

/-! ## The value of a parameter as an encoding -/

/-- A scalar parameter whose register holds the canonical representative of `x : ZMod p`
    denotes the encoding of `x`, at a modulus below `2 ^ 64`. -/
theorem AbiArg.read_eq_enc_zmod {p : ℕ} [NeZero p] (hp : p < 2 ^ 64) {x : AbiArg}
    (hk : x.kind = .scalar) (sa : AState) {v : ZMod p} (hv : (sa.regs x.reg).toNat = v.val) :
    x.read sa = enc v := by
  simp [AbiArg.read, hk, enc_zmod hp, hv]

/-- An array parameter of `n` words whose region holds the encodings of the elements of `v`
    denotes the encoding of `v`. -/
theorem AbiArg.read_eq_enc_words {α : Type} [HaxEnc α] {x : AbiArg} {n : Nat}
    (hk : x.kind = .words n) (sa : AState) {v : Array α}
    (hv : wordsAt sa.mem (sa.regs x.reg) n = v.toList.map enc) :
    x.read sa = enc v := by
  simp only [AbiArg.read, hk, hv]
  rfl

/-! ## Compiled bytes under a layout of scalars and arrays -/

/-- **Compiled bytes compute the function on scalars and word arrays.** The statement of
    `leanFront_correct` for a layout without constants whose parameters are scalars and word
    arrays in any order. The hypothesis on the canonical environment is that the bindings
    `ps a` are, parameter by parameter, the name of the parameter with the value it denotes
    at the entry state: the integer of its register for a scalar, the words at the address
    its register holds for an array (`AbiArg.read`). Then from every entry state satisfying
    the region conditions `σ.Regions`, the bytes decode to a program that halts in a state
    from which `σ` reads back the encoding of `f a`. -/
theorem leanFront_correct_mixed {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (te : TExpr)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA te σ fname = some (P, bytes)) (hsp : spineLamFree te.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres hax64WExit te.erase (fun a => bindParams (ps a)) G f)
    (hconsts : σ.consts = []) (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa)
    (a : A) (hG : G a)
    (hargs : List.Forall₂ (fun (x : AbiArg) (b : String × Value) =>
      b.1 = x.name ∧ b.2 = x.read sa) σ.args (ps a))
    (hn : narrowOk te σ = false := by rfl) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ σ.ResultOf sa sa' (enc (f a)) := by
  refine leanFront_correct te σ fname P bytes hc hsp ps G f hf hnd sa hsep a hG ?_ hn
  rw [canonEnv_eq_bindParams_read σ hconsts sa]
  congr 1
  generalize σ.args = l at hargs ⊢
  generalize ps a = m at hargs ⊢
  induction hargs with
  | nil => rfl
  | cons h _ ih => exact congrArg₂ _ (Prod.ext h.1.symm h.2.symm) ih

/-! ## An instance: two arrays and a scalar over BabyBear -/

/-- The element at `1` of `a` times `x`, plus the element at `2` of `b`, over BabyBear. -/
def mixLean (a : Array (ZMod 2013265921)) (x : ZMod 2013265921)
    (b : Array (ZMod 2013265921)) : ZMod 2013265921 :=
  _root_.Hax.index a 1 * x + _root_.Hax.index b 2

/-- The literal of `mixLean`. -/
def mixImp : ImpExpr := reifyField% mixLean

/-- The layout of `mixLean`: the array `a` of `4` words at `%rdi`, the scalar `x` in `%rsi`,
    the array `b` of `4` words at `%rdx`, no constant, the scalar result in `%rax`. -/
def mixAbi : AbiLayout :=
  AbiLayout.mk [⟨"a", "%rdi", .words 4⟩, ⟨"x", "%rsi", .scalar⟩, ⟨"b", "%rdx", .words 4⟩]
    [] (.reg "%rax") [] (-256) (-8) [] []

/-- The types of the parameters of `mixAbi`: two arrays of `4` words and one word. -/
def mixTypes : List (String × _root_.Hax.ImpType) :=
  [("a", .array (.uint .w64) 4), ("x", .uint .w64), ("b", .array (.uint .w64) 4)]

/-- The lift of `mixImp` under `mixTypes` exists (a test, checked by `rfl`). -/
theorem mixImp_toTExpr_isSome : (mixImp.toTExpr mixTypes).isSome = true := by
  rfl

/-- The typed literal of `mixLean`. -/
def mixT : TExpr := (mixImp.toTExpr mixTypes).get mixImp_toTExpr_isSome

/-- The erasure of the typed literal is the literal. -/
theorem mixT_erase : mixT.erase = mixImp :=
  ImpExpr.erase_toTExpr (Option.some_get mixImp_toTExpr_isSome).symm

/-- The BabyBear instance of `hax64WExit_index_zmod`. -/
theorem hax64WExit_index_babyBear (a : Array (ZMod 2013265921)) (i : Int) (h0 : 0 ≤ i)
    (h : i < (a.size : Int)) :
    hax64WExit "index" [enc a, .int i] = some (enc (_root_.Hax.index a i)) :=
  hax64WExit_index_zmod (by norm_num) a i h0 h

/-- From the entry environment binding `a`, `x`, `b`, the literal `mixImp` returns the
    encoding of `mixLean` under `hax64WExit`, for arrays `a` of more than `1` and `b` of more
    than `2` elements. -/
theorem mix_fnCorres :
    FnCorres hax64WExit mixImp
      (A := Array (ZMod 2013265921) × ZMod 2013265921 × Array (ZMod 2013265921) × Unit)
      (fun a => bindParams [("a", enc a.1), ("x", enc a.2.1), ("b", enc a.2.2.1)])
      (fun a => 1 < a.1.size ∧ 2 < a.2.2.1.size)
      (fun a => mixLean a.1 a.2.1 a.2.2.1) := by
  ascend_reified mixLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_index_babyBear]
    guard fun a => 1 < a.1.size ∧ 2 < a.2.2.1.size

/-- `compileA` accepts the typed literal of `mixLean` under `mixAbi` (checked by
    `native_decide`). -/
theorem mix_compileA_isSome : (compileA mixT mixAbi "mix").isSome = true := by
  native_decide

/-- **The compiled bytes of `mixLean`.** If `compileA` returns `(P, bytes)` on `mixT` under
    `mixAbi`, then from every entry state satisfying the region conditions of `mixAbi` whose
    regions at `%rdi` and `%rdx` hold the encodings of the `4` elements of `a` and `b` and
    whose `%rsi` holds the canonical representative of `x`, the bytes decode to a program
    that halts in a state whose `%rax` reads back the encoding of `mixLean a x b`. -/
theorem mix_bytes {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA mixT mixAbi "mix" = some (P, bytes)) (sa : AState)
    (hsep : mixAbi.Regions sa) (a b : Array (ZMod 2013265921)) (x : ZMod 2013265921)
    (ha : wordsAt sa.mem (sa.regs "%rdi") 4 = a.toList.map enc)
    (hx : (sa.regs "%rsi").toNat = x.val)
    (hb : wordsAt sa.mem (sa.regs "%rdx") 4 = b.toList.map enc) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ mixAbi.ResultOf sa sa' (enc (mixLean a x b)) := by
  have hf := mix_fnCorres
  rw [← mixT_erase] at hf
  have hla : a.size = 4 := by
    simpa [wordsAt] using (congrArg List.length ha).symm
  have hlb : b.size = 4 := by
    simpa [wordsAt] using (congrArg List.length hb).symm
  exact leanFront_correct_mixed mixT mixAbi "mix" P bytes hc (by rw [mixT_erase]; decide) _ _ _
    hf rfl (by decide) sa hsep (a, x, b, ()) ⟨by simp [hla], by simp [hlb]⟩
    (by
      simp only [mixAbi, List.forall₂_cons, List.Forall₂.nil, and_true]
      grind only [AbiArg.read_eq_enc_words, AbiArg.read_eq_enc_zmod])

/-- **`compileA` compiles `mixLean` correctly.** `compileA` returns bytes on `mixT` under
    `mixAbi`, and from every entry state as in `mix_bytes` they decode to a program that halts
    in a state whose `%rax` reads back the encoding of `mixLean a x b`. -/
theorem mix_compileA_correct : ∃ P bytes, compileA mixT mixAbi "mix" = some (P, bytes) ∧
    ∀ (sa : AState), mixAbi.Regions sa → ∀ (a b : Array (ZMod 2013265921))
      (x : ZMod 2013265921), wordsAt sa.mem (sa.regs "%rdi") 4 = a.toList.map enc →
      (sa.regs "%rsi").toNat = x.val → wordsAt sa.mem (sa.regs "%rdx") 4 = b.toList.map enc →
      ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
        ∧ mixAbi.ResultOf sa sa' (enc (mixLean a x b)) := by
  obtain ⟨⟨P, bytes⟩, hc⟩ := Option.isSome_iff_exists.mp mix_compileA_isSome
  exact ⟨P, bytes, hc, fun sa hsep a b x ha hx hb => mix_bytes hc sa hsep a b x ha hx hb⟩

end CatCrypt.Crypto.SecureCompilation.Haxc
