/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.ComToArithBlock

/-!
# The scalar prefix of a `Com jasminDialect`

`comToArithBlock` recognises a whole program and requires the return type
`.reg 64`. The `LowCT` descent produces a program of return type `.reg 0` whose
scalar operations are followed by a unit binder and a unit `ret`, so no whole
program of that shape is recognised.

`comScalarPrefix` recognises the leading run of covered 64-bit bindings —
`regArith`, `shlImm`/`shrImm` with a count below the word width, `regConst`, and
the element load and store whose index operand names a slot bound by an earlier
`regConst` binder — of a program of any return type, returning that run as an
`ArithBlock` together with the remaining program as a tail over the block's
final context. A program whose *first* binding is an element store is rejected,
since the block's return variable is a `reg 64` slot and no such slot is bound
yet.
`ArithBlock.toComWith` reassembles a block and a tail into one program, and
`comScalarPrefix_toComWith` states that the prefix and the tail reassemble to
the program they were recognised from.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin

/-! ## 1. The final context of a block, and assembly with a tail -/

/-- **The context a block's last operation leaves behind.** A `.ret` binds
    nothing, so the final context is the block's own context; a `.op` binds one
    `reg 64` slot before the rest of the block. -/
def ArithBlock.finalCtx : {Γ : Ctxt jasminDialect} → ArithBlock Γ →
    Ctxt jasminDialect
  | Γ, .ret _ => Γ
  | _, .op _ _ _ _ rest => rest.finalCtx
  | _, .un _ _ _ rest => rest.finalCtx
  | _, .cnst _ rest => rest.finalCtx
  | _, .load _ _ _ _ _ _ rest => rest.finalCtx
  | _, .store _ _ _ _ _ _ _ rest => rest.finalCtx

/-- **Compile a block and a tail into one program.** Each `.op` becomes a
    `Com.var` binding `arithExpr`, as in `ArithBlock.toCom`, and the block's
    `.ret` is replaced by the given continuation over the block's final
    context. -/
def ArithBlock.toComWith : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (ab : ArithBlock Γ) → Com jasminDialect ab.finalCtx t → Com jasminDialect Γ t
  | _, _, .ret _, tail => tail
  | _, _, .op bop _ a b rest, tail => .var (arithExpr bop a b) (rest.toComWith tail)
  | _, _, .un uop _ a rest, tail => .var (unExpr uop a) (rest.toComWith tail)
  | _, _, .cnst n rest, tail => .var (constExpr n) (rest.toComWith tail)
  | _, _, .load _ _ _ _ arr i rest, tail => .var (loadExpr arr i) (rest.toComWith tail)
  | _, _, .store _ _ _ _ arr i src rest, tail =>
      .var (storeExpr arr i src) (rest.toComWith tail)

/-! ## 2. The prefix recogniser -/

/-- **The scalar run of a program, continuing from a given slot.** Collects the
    leading covered 64-bit bindings of `c` into a block terminated by `.ret v0`,
    and returns the first unrecognised program as the tail. Total: a program whose
    first binding is not covered gives the block `.ret v0` and `c` itself as the
    tail. -/
def comScalarTailFrom : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    (v0 : Ctxt.Var Γ (.reg 64)) → (c : Com jasminDialect Γ t) →
    (κ : ConstEnv Γ := fun _ => none) →
    (ab : ArithBlock Γ) × Com jasminDialect ab.finalCtx t
  | _, _, v0, .ret v, _ => ⟨.ret v0, .ret v⟩
  | _, _, v0, .var (t := t') e body, κ =>
      match t', e, body with
      | JasminTy.reg 64, ⟨.regArith bop 64, hop, args⟩, body' =>
          if hs : isScalarBopB bop = true then
            ⟨.op bop (IsScalarBop_of_isScalarBopB hs) args.head args.tail.head
                (comScalarTailFrom .here body' (κ.extend none)).1,
              (comScalarTailFrom .here body' (κ.extend none)).2⟩
          else ⟨.ret v0, .var (Expr.mk (.regArith bop 64) hop args) body'⟩
      | JasminTy.reg 64, ⟨.shlImm 64 k, hop, args⟩, body' =>
          if hk : k < 64 then
            ⟨.un (unOfShl k) (IsScalarUn_unOfShl hk) args.head
                (comScalarTailFrom .here body' (κ.extend none)).1,
              (comScalarTailFrom .here body' (κ.extend none)).2⟩
          else ⟨.ret v0, .var (Expr.mk (.shlImm 64 k) hop args) body'⟩
      | JasminTy.reg 64, ⟨.shrImm 64 k, hop, args⟩, body' =>
          if hk : k < 64 then
            ⟨.un (.shr k) hk args.head
                (comScalarTailFrom .here body' (κ.extend none)).1,
              (comScalarTailFrom .here body' (κ.extend none)).2⟩
          else ⟨.ret v0, .var (Expr.mk (.shrImm 64 k) hop args) body'⟩
      | JasminTy.reg 64, ⟨.regConst 64 n, _, _⟩, body' =>
          ⟨.cnst n (comScalarTailFrom .here body' (κ.extend (some n))).1,
            (comScalarTailFrom .here body' (κ.extend (some n))).2⟩
      | JasminTy.reg 64, ⟨.stackLoad 64 n, hop, args⟩, body' =>
          match κ args.tail.head with
          | some k =>
              if hk : isDispIndexB k = true then
                ⟨.load n k (IsDispIndex_of_isDispIndexB hk) (arrBase args.head)
                    args.head args.tail.head
                    (comScalarTailFrom .here body' (κ.extend none)).1,
                  (comScalarTailFrom .here body' (κ.extend none)).2⟩
              else ⟨.ret v0, .var (Expr.mk (.stackLoad 64 n) hop args) body'⟩
          | none => ⟨.ret v0, .var (Expr.mk (.stackLoad 64 n) hop args) body'⟩
      | JasminTy.stackArr 64 n, ⟨.stackStore 64 _, rfl, args⟩, body' =>
          match κ args.tail.head with
          | some k =>
              if hk : isDispIndexB k = true then
                ⟨.store n k (IsDispIndex_of_isDispIndexB hk) (arrBase args.head)
                    args.head args.tail.head args.tail.tail.head
                    (comScalarTailFrom (.there v0) body' (ConstEnv.shiftArr κ)).1,
                  (comScalarTailFrom (.there v0) body' (ConstEnv.shiftArr κ)).2⟩
              else ⟨.ret v0, .var (Expr.mk (.stackStore 64 n) rfl args) body'⟩
          | none => ⟨.ret v0, .var (Expr.mk (.stackStore 64 n) rfl args) body'⟩
      | _, e', body' => ⟨.ret v0, .var e' body'⟩

/-- **Recognise the leading scalar operations of a dialect program.** A program
    whose first binding is covered — a scalar 64-bit `regArith`, a 64-bit
    `shlImm`/`shrImm` with a count below the word width, or a 64-bit `regConst` —
    yields the block of its leading covered operations together with the remaining
    program over that block's final context; every other program is rejected,
    since a block returns a `reg 64` slot and no such slot is bound yet. -/
def comScalarPrefix : {Γ : Ctxt jasminDialect} → {t : JasminTy} →
    Com jasminDialect Γ t → (κ : ConstEnv Γ := fun _ => none) →
    Option ((ab : ArithBlock Γ) × Com jasminDialect ab.finalCtx t)
  | _, _, .ret _, _ => none
  | _, _, .var (t := t') e body, κ =>
      match t', e, body with
      | JasminTy.reg 64, ⟨.regArith bop 64, _, args⟩, body =>
          if hs : isScalarBopB bop = true then
            some ⟨.op bop (IsScalarBop_of_isScalarBopB hs) args.head args.tail.head
                (comScalarTailFrom .here body (κ.extend none)).1,
              (comScalarTailFrom .here body (κ.extend none)).2⟩
          else none
      | JasminTy.reg 64, ⟨.shlImm 64 k, _, args⟩, body =>
          if hk : k < 64 then
            some ⟨.un (unOfShl k) (IsScalarUn_unOfShl hk) args.head
                (comScalarTailFrom .here body (κ.extend none)).1,
              (comScalarTailFrom .here body (κ.extend none)).2⟩
          else none
      | JasminTy.reg 64, ⟨.shrImm 64 k, _, args⟩, body =>
          if hk : k < 64 then
            some ⟨.un (.shr k) hk args.head
                (comScalarTailFrom .here body (κ.extend none)).1,
              (comScalarTailFrom .here body (κ.extend none)).2⟩
          else none
      | JasminTy.reg 64, ⟨.regConst 64 n, _, _⟩, body =>
          some ⟨.cnst n (comScalarTailFrom .here body (κ.extend (some n))).1,
            (comScalarTailFrom .here body (κ.extend (some n))).2⟩
      | JasminTy.reg 64, ⟨.stackLoad 64 n, _, args⟩, body =>
          match κ args.tail.head with
          | some k =>
              if hk : isDispIndexB k = true then
                some ⟨.load n k (IsDispIndex_of_isDispIndexB hk) (arrBase args.head)
                    args.head args.tail.head
                    (comScalarTailFrom .here body (κ.extend none)).1,
                  (comScalarTailFrom .here body (κ.extend none)).2⟩
              else none
          | none => none
      | _, _, _ => none

/-! ## 3. The round trip -/

/-- **The scalar run reassembles.** The block and tail of `comScalarTailFrom`
    compile back to the program they were read from. -/
theorem comScalarTailFrom_toComWith {Γ : Ctxt jasminDialect} {t : JasminTy}
    (v0 : Ctxt.Var Γ (.reg 64)) (c : Com jasminDialect Γ t) (κ : ConstEnv Γ) :
    (comScalarTailFrom v0 c κ).1.toComWith (comScalarTailFrom v0 c κ).2 = c := by
  induction v0, c, κ using comScalarTailFrom.induct with
  | case1 => rfl
  | case2 =>
      rename_i bop hop args hs v0 κ body ih
      rw [comScalarTailFrom, dite_eq_left hs]
      simp only [ArithBlock.toComWith, arithExpr, hvector_two_eta args]
      rw [ih]
  | case3 =>
      rename_i bop hop args hs v0 κ body
      rw [comScalarTailFrom, dite_eq_right hs]
      simp only [ArithBlock.toComWith]
      rfl
  | case4 =>
      rename_i k hop args hk v0 κ body ih
      rw [comScalarTailFrom, dite_eq_left hk]
      simp only [ArithBlock.toComWith, unExpr_unOfShl, hvector_one_eta args]
      rw [ih]
  | case5 =>
      rename_i k hop args hk v0 κ body
      rw [comScalarTailFrom, dite_eq_right hk]
      simp only [ArithBlock.toComWith]
      rfl
  | case6 =>
      rename_i k hop args hk v0 κ body ih
      rw [comScalarTailFrom, dite_eq_left hk]
      simp only [ArithBlock.toComWith, unExpr, hvector_one_eta args]
      rw [ih]
  | case7 =>
      rename_i k hop args hk v0 κ body
      rw [comScalarTailFrom, dite_eq_right hk]
      simp only [ArithBlock.toComWith]
      rfl
  | case8 =>
      rename_i n hop args v0 κ body ih
      rw [comScalarTailFrom]
      simp only [ArithBlock.toComWith, constExpr, hvector_nil_eta args]
      rw [ih]
  | case9 =>
      rename_i n hop args k hk v0 κ body hκ ih
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        dsimp only
        rw [dite_eq_left hk]
        simp only [ArithBlock.toComWith, loadExpr, hvector_two_eta args]
        rw [ih]
      · rename_i heq
        rw [hκ] at heq
        exact absurd heq (by simp)
  | case10 =>
      rename_i n hop args k hk v0 κ body hκ
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        dsimp only
        rw [dite_eq_right hk]
        simp only [ArithBlock.toComWith]
        rfl
      · rename_i heq
        rw [hκ] at heq
        exact absurd heq (by simp)
  | case11 =>
      rename_i n hop args v0 κ body hκ
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        exact absurd heq (by simp)
      · simp only [ArithBlock.toComWith]
        rfl
  | case12 =>
      rename_i n args k hk v0 κ body hκ ih
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        dsimp only
        rw [dite_eq_left hk]
        simp only [ArithBlock.toComWith, storeExpr, hvector_three_eta args]
        rw [ih]
      · rename_i heq
        rw [hκ] at heq
        exact absurd heq (by simp)
  | case13 =>
      rename_i n args k hk v0 κ body hκ
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        dsimp only
        rw [dite_eq_right hk]
        simp only [ArithBlock.toComWith]
        rfl
      · rename_i heq
        rw [hκ] at heq
        exact absurd heq (by simp)
  | case14 =>
      rename_i n args v0 κ body hκ
      rw [comScalarTailFrom]
      split
      · rename_i k' heq
        rw [hκ] at heq
        exact absurd heq (by simp)
      · simp only [ArithBlock.toComWith]
        rfl
  | case15 =>
      rw [comScalarTailFrom] <;>
        first
          | assumption
          | (simp only [ArithBlock.toComWith]; rfl)

/-- **The recogniser invents nothing and drops nothing.** A recognised prefix and
    its tail reassemble to the program they were recognised from. -/
theorem comScalarPrefix_toComWith_sigma {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (κ : ConstEnv Γ)
    (p : (ab : ArithBlock Γ) × Com jasminDialect ab.finalCtx t)
    (h : comScalarPrefix c κ = some p) : p.1.toComWith p.2 = c := by
  fun_cases comScalarPrefix c κ
  case case1 => simp [comScalarPrefix] at h
  case case2 =>
      rename_i bop hop hs args body
      rw [comScalarPrefix, dite_eq_left hs] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [ArithBlock.toComWith, arithExpr, hvector_two_eta args]
      rw [comScalarTailFrom_toComWith .here body]
  case case3 =>
      rename_i bop hop hs args body
      rw [comScalarPrefix, dite_eq_right hs] at h
      exact absurd h (by simp)
  case case4 =>
      rename_i k hop hk args body
      rw [comScalarPrefix, dite_eq_left hk] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [ArithBlock.toComWith, unExpr_unOfShl, hvector_one_eta args]
      rw [comScalarTailFrom_toComWith .here body]
  case case5 =>
      rename_i k hop hk args body
      rw [comScalarPrefix, dite_eq_right hk] at h
      exact absurd h (by simp)
  case case6 =>
      rename_i k hop hk args body
      rw [comScalarPrefix, dite_eq_left hk] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [ArithBlock.toComWith, unExpr, hvector_one_eta args]
      rw [comScalarTailFrom_toComWith .here body]
  case case7 =>
      rename_i k hop hk args body
      rw [comScalarPrefix, dite_eq_right hk] at h
      exact absurd h (by simp)
  case case8 =>
      rename_i n hop args body
      rw [comScalarPrefix] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [ArithBlock.toComWith, constExpr, hvector_nil_eta args]
      rw [comScalarTailFrom_toComWith .here body]
  case case9 =>
      rename_i n hop k hk args body hκ
      rw [comScalarPrefix] at h
      simp only [hκ] at h
      rw [dite_eq_left hk] at h
      simp only [Option.some.injEq] at h
      subst h
      simp only [ArithBlock.toComWith, loadExpr, hvector_two_eta args]
      rw [comScalarTailFrom_toComWith .here body]
  case case10 =>
      rename_i n hop k hk args body hκ
      rw [comScalarPrefix] at h
      simp only [hκ] at h
      rw [dite_eq_right hk] at h
      exact absurd h (by simp)
  case case11 =>
      rename_i n hop args body hκ
      rw [comScalarPrefix] at h
      simp [hκ] at h
  case case12 =>
      rw [comScalarPrefix] at h <;>
        first
          | exact absurd h (by simp)
          | assumption

/-- **The recogniser invents nothing and drops nothing.** A recognised prefix and
    its tail reassemble to the program they were recognised from. -/
theorem comScalarPrefix_toComWith {Γ : Ctxt jasminDialect} {t : JasminTy}
    (c : Com jasminDialect Γ t) (κ : ConstEnv Γ) (ab : ArithBlock Γ)
    (tail : Com jasminDialect ab.finalCtx t)
    (h : comScalarPrefix c κ = some ⟨ab, tail⟩) : ab.toComWith tail = c :=
  comScalarPrefix_toComWith_sigma c κ ⟨ab, tail⟩ h

/-! ## 4. Non-vacuity — a scalar prefix followed by a unit tail

The shape the `LowCT` descent produces: the scalar operations, then a unit
binder and a `ret` of that unit slot. -/

/-- A two-op dialect program over `Δ2` ending in a unit binder and a unit
    return: `s1 := a + b ; s2 := s1 * a ; u := 0 ; ret u`. -/
def comBlock2Unit : Com jasminDialect Δ2 (.reg 0) :=
  .var (.mk (.regArith .add 64) rfl (.cons dA (.cons dB .nil)))
    (.var (.mk (.regArith .mul 64) rfl (.cons .here (.cons (.there .here) .nil)))
      (.var (.mk (.regConst 0 0) rfl .nil) (.ret .here)))

/-- The unit tail of `comBlock2Unit`, over the context the two operations
    leave behind. -/
def comBlock2UnitTail : Com jasminDialect (.reg 64 :: .reg 64 :: Δ2) (.reg 0) :=
  .var (.mk (.regConst 0 0) rfl .nil) (.ret .here)

/-- The program's scalar prefix is the two-operation block `block2`, and its tail
    is the unit binder and return. -/
theorem comBlock2Unit_prefix :
    comScalarPrefix comBlock2Unit = some ⟨block2, comBlock2UnitTail⟩ := by
  with_unfolding_all rfl

/-- The recognised prefix and tail reassemble to the program. -/
theorem comBlock2Unit_toComWith :
    block2.toComWith comBlock2UnitTail = comBlock2Unit :=
  comScalarPrefix_toComWith comBlock2Unit _ block2 comBlock2UnitTail comBlock2Unit_prefix

/-! ## 5. Non-vacuity — a prefix led by a constant

The mixed five-binder program of `ComToArithBlock`, followed by a unit binder
and a unit return: the leading binder is a `regConst`, and the prefix recogniser
accepts it. -/

/-- The five-binder mixed program followed by a unit binder and a unit return.
    Its leading binder is a `regConst`. -/
def comBlock3Unit : Com jasminDialect Δ2 (.reg 0) :=
  .var (.mk (.regConst 64 5) rfl .nil)
    (.var (.mk (.shlImm 64 0) rfl (.cons (.there .here) .nil))
      (.var (.mk (.shlImm 64 3) rfl (.cons .here .nil))
        (.var (.mk (.shrImm 64 2) rfl
            (.cons (.there (.there (.there (.there .here)))) .nil))
          (.var (.mk (.regArith .xor 64) rfl (.cons (.there .here) (.cons .here .nil)))
            (.var (.mk (.regConst 0 0) rfl .nil) (.ret .here))))))

/-- The unit tail of `comBlock3Unit`, over the context the five binders leave
    behind. -/
def comBlock3UnitTail :
    Com jasminDialect
      (.reg 64 :: .reg 64 :: .reg 64 :: .reg 64 :: .reg 64 :: Δ2) (.reg 0) :=
  .var (.mk (.regConst 0 0) rfl .nil) (.ret .here)

/-- **A prefix whose leading binder is a constant is recognised.** The scalar
    prefix of `comBlock3Unit` is the mixed block `block3`, and its tail is the
    unit binder and return. -/
theorem comBlock3Unit_prefix :
    comScalarPrefix comBlock3Unit = some ⟨block3, comBlock3UnitTail⟩ := by
  with_unfolding_all rfl

/-- The recognised prefix and tail reassemble to the program. -/
theorem comBlock3Unit_toComWith :
    block3.toComWith comBlock3UnitTail = comBlock3Unit :=
  comScalarPrefix_toComWith comBlock3Unit _ block3 comBlock3UnitTail comBlock3Unit_prefix

/-! ## 6. Non-vacuity — a prefix with a load and a store

The load–compute–store program of `ComToArithBlock`, followed by a unit binder
and a unit return: the prefix recogniser carries both memory binders and stops
at the unit binder. -/

/-- The load–compute–store program followed by a unit binder and a unit
    return. -/
def comBlock4Unit : Com jasminDialect Δm (.reg 0) :=
  .var (.mk (.regConst 64 1) rfl .nil)
    (.var (.mk (.stackLoad 64 4) rfl (.cons (.there .here) (.cons .here .nil)))
      (.var (.mk (.shlImm 64 1) rfl (.cons .here .nil))
        (.var (.mk (.regConst 64 2) rfl .nil)
          (.var (.mk (.stackStore 64 4) rfl
              (.cons (.there (.there (.there (.there .here))))
                (.cons .here (.cons (.there .here) .nil))))
            (.var (.mk (.regConst 0 0) rfl .nil) (.ret .here))))))

/-- The unit tail of `comBlock4Unit`, over the context the memory block leaves
    behind. -/
def comBlock4UnitTail :
    Com jasminDialect
      (.stackArr 64 4 :: .reg 64 :: .reg 64 :: .reg 64 :: .reg 64 :: Δm) (.reg 0) :=
  .var (.mk (.regConst 0 0) rfl .nil) (.ret .here)

/-- The block of `comBlock4Unit`'s binders as the prefix recogniser returns it:
    the binders of `block4`, returning the slot bound last before the tail —
    the second index constant. -/
def block4Unit : ArithBlock Δm :=
  .cnst 1
    (.load 4 1 (show IsDispIndex 1 by unfold IsDispIndex; omega) "mem"
        (.there .here) .here
      (.un (.shl 1) (show (1 : Nat) < 64 by omega) .here
        (.cnst 2
          (.store 4 2 (show IsDispIndex 2 by unfold IsDispIndex; omega) "mem"
              (.there (.there (.there (.there .here)))) .here (.there .here)
            (.ret (.there .here))))))

/-- **A prefix carrying both memory binders is recognised.** The scalar prefix of
    `comBlock4Unit` is its five binders, and its tail is the unit binder and
    return. -/
theorem comBlock4Unit_prefix :
    comScalarPrefix comBlock4Unit = some ⟨block4Unit, comBlock4UnitTail⟩ := by
  with_unfolding_all rfl

/-- The recognised memory prefix and its tail reassemble to the program. -/
theorem comBlock4Unit_toComWith :
    block4Unit.toComWith comBlock4UnitTail = comBlock4Unit :=
  comScalarPrefix_toComWith comBlock4Unit _ block4Unit comBlock4UnitTail
    comBlock4Unit_prefix

end CatCrypt.Crypto.SecureCompilation.Ascent
