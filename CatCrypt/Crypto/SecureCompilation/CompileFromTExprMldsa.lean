/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.TExprToThir

/-!
# ML-DSA through the typed front, from the emitted `Hax.TExpr` literals

The typed front `TExprToThir.texprToThir` applied to the ML-DSA typed literals
that `haxpipeT --emit-certified` produces. The literals are copied verbatim from
the ML-DSA extraction; nothing in this module is hand-authored source.

The subset `texprToThir` accepts is the let-normalized scalar ARX fragment with
atom-only operator arguments at a single register width. Of the ML-DSA literals,
the parameter constants are inside it and the modular-arithmetic functions are
outside it; both facts are recorded as theorems, so the front's ML-DSA coverage
is machine-checked rather than described.

## Main definitions

* `qTexpr`, `zetaTexpr`, `qinvTexpr`, `invNttFTexpr` — the emitted typed
  literals of the ML-DSA parameters `Q`, `ZETA`, `QINV`, `INV_NTT_F`.
* `modQTexpr`, `addModQTexpr`, `subModQTexpr`, `mulModQTexpr`, `modPmTexpr`,
  `power2roundTexpr`, `montReduceTexpr` — the emitted typed literals of the
  ML-DSA modular-arithmetic functions.

## Main results

* `qTexpr_texprToThir`, `qTexpr_denoteScalarT`, `q_texpr_compiles` — the
  emitted `Q` literal translates to a front `Thir`, denotes to `8380417` at
  width 32, and lowers to a `Com jasminDialect` denoting the same value.
* `zetaTexpr_denoteScalarT`, `qinvTexpr_denoteScalarT`,
  `invNttFTexpr_denoteScalarT` — the same value theorem for the other three
  parameter constants.
* `modQTexpr_rejected`, `addModQTexpr_rejected`, `subModQTexpr_rejected`,
  `mulModQTexpr_rejected`, `modPmTexpr_rejected`, `power2roundTexpr_rejected`,
  `montReduceTexpr_rejected` — the typed front returns `none` on each of the
  ML-DSA modular-arithmetic literals.
* `recogBinTy_Rem`, `recogShiftTy_Rem`, `recogCastTy_Rem`, `recogBinTy_Div` —
  the head `"Rem"` (and `"Div"`) is recognised by no operator reader of the
  typed front.
* `recogCastTy_cast_i32`, `recogCastTy_cast_u32`, `recogCastTy_cast_i64` —
  the signed/named coercion heads of the extraction are recognised by no
  reader either.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.CompileFromTExprMldsa

open Hax
open CatCrypt.Crypto.SecureCompilation.ThirToComFront
open CatCrypt.Crypto.SecureCompilation.TExprToThir
open CatCrypt.Crypto.SecureCompilation.VIR (Com)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (jasminDialect)

/-! ## §1  The emitted type abbreviations

The `ty_<i>` names of the ML-DSA extraction, redeclared here with the same
spelling so the copied literals below are character-identical to the emitted
ones. Only the ones the copied literals mention are declared. -/

/-- `i32`, the extraction's `ty_43`. -/
abbrev ty_43 : ImpType := (.sint .w32)
/-- `i64`, the extraction's `ty_44`. -/
abbrev ty_44 : ImpType := (.sint .w64)
/-- `(u32, i32)`, the extraction's `ty_52`. -/
abbrev ty_52 : ImpType := (.tuple [(.uint .w32), (.sint .w32)])
/-- `u32`, the extraction's `ty_55`. This is the ML-DSA coefficient type. -/
abbrev ty_55 : ImpType := (.uint .w32)
/-- `u64`, the extraction's `ty_56`, the intermediate type of the modular
    arithmetic. -/
abbrev ty_56 : ImpType := (.uint .w64)
/-- The extraction's `ty_59`, carried by nodes the frontend left untyped. -/
abbrev ty_59 : ImpType := .unknown

/-! ## §2  The emitted ML-DSA typed literals, verbatim

Each definition below is the body of the correspondingly named
`Mldsa.<name>_texpr` of
`CatCrypt/Crypto/MLDSA/Extraction/Mldsa_haxpipe.lean` in the SSProve-lean tree
at commit `aaf71668a`, copied character for character. The extraction also
carries `example : <name>_texpr.erase = <name>_impExpr := rfl` for each one, so
the literal is tied to the untyped expression the rest of the extraction uses.

To re-check a copy against the extraction:

```
grep -A 1 '^def add_mod_q_texpr' \
  ../SSProve-lean/CatCrypt/Crypto/MLDSA/Extraction/Mldsa_haxpipe.lean
```

(and likewise for `Q`, `ZETA`, `QINV`, `INV_NTT_F`, `mod_q`, `sub_mod_q`,
`mul_mod_q`, `mod_pm`, `power2round`, `mont_reduce`). The dev tree cannot be
imported from this package: the Lake dependency runs dev → compiler. -/

/-- The emitted `Mldsa.Q_texpr`: the ML-DSA modulus `q = 8380417 = 2^23 - 2^13 + 1`
    (FIPS 204 §4). -/
def qTexpr : Hax.TExpr :=
  (.mk (.lit (ImpLit.int 8380417)) ty_55)

/-- The emitted `Mldsa.ZETA_texpr`: the 512-th root of unity `1753` modulo `q`
    used by the ML-DSA NTT (FIPS 204 §7.5). -/
def zetaTexpr : Hax.TExpr :=
  (.mk (.lit (ImpLit.int 1753)) ty_55)

/-- The emitted `Mldsa.QINV_texpr`: `58728449`, the Montgomery constant
    `-q⁻¹ mod 2^32` of the ML-DSA reduction. -/
def qinvTexpr : Hax.TExpr :=
  (.mk (.lit (ImpLit.int 58728449)) ty_55)

/-- The emitted `Mldsa.INV_NTT_F_texpr`: `8347681`, the scaling factor applied
    after the inverse NTT. -/
def invNttFTexpr : Hax.TExpr :=
  (.mk (.lit (ImpLit.int 8347681)) ty_55)

/-- The emitted `Mldsa.mod_q_texpr`: `mod_q a` is `a % q` on `u32`
    representatives. -/
def modQTexpr : Hax.TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_55) (.mk (.app "Rem" [(.mk (.var "a") ty_55), (.mk (.var "Q") ty_55)]) ty_55)) ty_55)

/-- The emitted `Mldsa.add_mod_q_texpr`: `add_mod_q a b` is `(a + b) % q` on
    `u32` representatives, computed through `u64` intermediates. The dev-tree
    theorem `CatCrypt.Crypto.MLDSA.Transfer.Scalar.add_mod_q_eq` states that
    meaning over `Int`. -/
def addModQTexpr : Hax.TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_55) (.mk (.letBind "b" (.mk (.var "b") ty_55) (.mk (.app "cast#32" [(.mk (.app "Rem" [(.mk (.app "Add" [(.mk (.app "cast#64" [(.mk (.var "a") ty_55)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "b") ty_55)]) ty_56)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "Q") ty_55)]) ty_56)]) ty_56)]) ty_55)) ty_55)) ty_55)

/-- The emitted `Mldsa.sub_mod_q_texpr`: `sub_mod_q a b` is `(a + q - b % q) % q`
    on `u32` representatives, computed through `u64` intermediates. -/
def subModQTexpr : Hax.TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_55) (.mk (.letBind "b" (.mk (.var "b") ty_55) (.mk (.app "cast#32" [(.mk (.app "Rem" [(.mk (.app "Sub" [(.mk (.app "Add" [(.mk (.app "cast#64" [(.mk (.var "a") ty_55)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "Q") ty_55)]) ty_56)]) ty_56), (.mk (.app "cast#64" [(.mk (.app "Rem" [(.mk (.var "b") ty_55), (.mk (.var "Q") ty_55)]) ty_55)]) ty_56)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "Q") ty_55)]) ty_56)]) ty_56)]) ty_55)) ty_55)) ty_55)

/-- The emitted `Mldsa.mul_mod_q_texpr`: `mul_mod_q a b` is `(a * b) % q` on
    `u32` representatives, computed through `u64` intermediates. -/
def mulModQTexpr : Hax.TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_55) (.mk (.letBind "b" (.mk (.var "b") ty_55) (.mk (.app "cast#32" [(.mk (.app "Rem" [(.mk (.app "Mul" [(.mk (.app "cast#64" [(.mk (.var "a") ty_55)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "b") ty_55)]) ty_56)]) ty_56), (.mk (.app "cast#64" [(.mk (.var "Q") ty_55)]) ty_56)]) ty_56)]) ty_55)) ty_55)) ty_55)

/-- The emitted `Mldsa.mod_pm_texpr`: `mod_pm x alpha` is the centered
    representative of `x` modulo `alpha` on `i32` (FIPS 204 §2.3 `mod±`). -/
def modPmTexpr : Hax.TExpr :=
  (.mk (.letBind "x" (.mk (.var "x") ty_43) (.mk (.letBind "alpha" (.mk (.var "alpha") ty_43) (.mk (.letBind "r" (.mk (.app "Rem#i32" [(.mk (.var "x") ty_43), (.mk (.var "alpha") ty_43)]) ty_43) (.mk (.ifThenElse (.mk (.app "Gt" [(.mk (.var "r") ty_43), (.mk (.app "Div#i32" [(.mk (.var "alpha") ty_43), (.mk (.lit (ImpLit.int 2)) ty_43)]) ty_43)]) .bool) (.mk (.app "Sub" [(.mk (.var "r") ty_43), (.mk (.var "alpha") ty_43)]) ty_43) (.mk (.var "r") ty_43)) ty_43)) ty_43)) ty_43)) ty_43)

/-- The emitted `Mldsa.power2round_texpr`: `power2round r` splits `r mod q` into
    the high part `r₁` and the centered low part `r₀` at the radix `2^d`
    (FIPS 204 §7.4 `Power2Round`). -/
def power2roundTexpr : Hax.TExpr :=
  (.mk (.letBind "r" (.mk (.var "r") ty_55) (.mk (.letBind "r_plus" (.mk (.app "cast#i32" [(.mk (.app "Rem" [(.mk (.var "r") ty_55), (.mk (.var "Q") ty_55)]) ty_55)]) ty_43) (.mk (.letBind "r0" (.mk (.app "mod_pm" [(.mk (.var "r_plus") ty_43), (.mk (.app "Shl#i32" [(.mk (.lit (ImpLit.int 1)) ty_43), (.mk (.var "D") ty_55)]) ty_43)]) ty_43) (.mk (.tuple [(.mk (.app "cast#u32" [(.mk (.app "Shr#i32" [(.mk (.app "Sub" [(.mk (.var "r_plus") ty_43), (.mk (.var "r0") ty_43)]) ty_43), (.mk (.var "D") ty_55)]) ty_43)]) ty_55), (.mk (.var "r0") ty_43)]) ty_52)) ty_59)) ty_52)) ty_52)

/-- The emitted `Mldsa.mont_reduce_texpr`: `mont_reduce a` is the Montgomery
    reduction of an `i64` product to an `i32` representative. -/
def montReduceTexpr : Hax.TExpr :=
  (.mk (.letBind "a" (.mk (.var "a") ty_44) (.mk (.letBind "t" (.mk (.app "wrapping_mul#i32" [(.mk (.app "cast#i32" [(.mk (.var "a") ty_44)]) ty_43), (.mk (.app "cast#i32" [(.mk (.var "QINV") ty_55)]) ty_43)]) ty_43) (.mk (.app "cast#i32" [(.mk (.app "Shr#i64" [(.mk (.app "Sub" [(.mk (.var "a") ty_44), (.mk (.app "Mul" [(.mk (.app "cast#i64" [(.mk (.var "t") ty_43)]) ty_44), (.mk (.app "cast#i64" [(.mk (.var "Q") ty_55)]) ty_44)]) ty_44)]) ty_44), (.mk (.lit (ImpLit.int 32)) ty_43)]) ty_44)]) ty_43)) ty_43)) ty_43)

/-! ## §3  The parameter constants compile

A `.lit` node is inside the typed front's subset: `texprToThir` maps it to
`Thir.ret (Atom.lit n)`, and `texprToThir_denoteScalarT` carries the value. -/

/-- The emitted `Q` literal translates to the front `Thir` returning `8380417`. -/
theorem qTexpr_texprToThir : texprToThir [] qTexpr = some (Thir.ret (Atom.lit 8380417)) := rfl

/-- The emitted `ZETA` literal translates to the front `Thir` returning `1753`. -/
theorem zetaTexpr_texprToThir :
    texprToThir [] zetaTexpr = some (Thir.ret (Atom.lit 1753)) := rfl

/-- The emitted `QINV` literal translates to the front `Thir` returning
    `58728449`. -/
theorem qinvTexpr_texprToThir :
    texprToThir [] qinvTexpr = some (Thir.ret (Atom.lit 58728449)) := rfl

/-- The emitted `INV_NTT_F` literal translates to the front `Thir` returning
    `8347681`. -/
theorem invNttFTexpr_texprToThir :
    texprToThir [] invNttFTexpr = some (Thir.ret (Atom.lit 8347681)) := rfl

/-- The emitted `Q` literal denotes, under the typed source semantics at width
    32, to the ML-DSA modulus `8380417`. -/
theorem qTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) :
    TExpr.denoteScalarT [] I qTexpr ρ = some (BitVec.ofNat 32 8380417) := rfl

/-- The emitted `ZETA` literal denotes, at width 32, to `1753`. -/
theorem zetaTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) :
    TExpr.denoteScalarT [] I zetaTexpr ρ = some (BitVec.ofNat 32 1753) := rfl

/-- The emitted `QINV` literal denotes, at width 32, to `58728449`. -/
theorem qinvTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) :
    TExpr.denoteScalarT [] I qinvTexpr ρ = some (BitVec.ofNat 32 58728449) := rfl

/-- The emitted `INV_NTT_F` literal denotes, at width 32, to `8347681`. -/
theorem invNttFTexpr_denoteScalarT {nIn : Nat} (I : Fin nIn → BitVec 32)
    (ρ : String → Option (BitVec 32)) :
    TExpr.denoteScalarT [] I invNttFTexpr ρ = some (BitVec.ofNat 32 8347681) := rfl

/-- **The emitted ML-DSA `Q` literal, compiled end to end through the typed
    front.** There is a front `Thir` `t` and a `Com jasminDialect` `c` such that
    the emitted typed literal translates to `t` via `texprToThir`, `t` lowers to
    `c` through the committed `thirToJasmin` back half, and `c` denotes to
    `8380417`, the ML-DSA modulus `q = 2^23 - 2^13 + 1` of FIPS 204 §4. -/
theorem q_texpr_compiles :
    ∃ (t : Thir) (c : Com jasminDialect (frontCtxt 32 0 []) (rW 32)),
      texprToThir [] qTexpr = some t ∧
      thirToJasmin [] (initFState 32 0) t = some c ∧
      ∀ (I : Fin 0 → BitVec 32),
        c.denote (inputValuation 32 0 I) = BitVec.ofNat 32 8380417 := by
  have hcSome :
      (thirToJasmin [] (initFState 32 0) (Thir.ret (Atom.lit 8380417))).isSome := by
    simp [thirToJasmin, rhsExpr]
  set c := (thirToJasmin [] (initFState 32 0) (Thir.ret (Atom.lit 8380417))).get hcSome
    with hc_def
  have hc : thirToJasmin [] (initFState 32 0) (Thir.ret (Atom.lit 8380417)) = some c :=
    (Option.some_get _).symm
  refine ⟨_, c, qTexpr_texprToThir, hc, ?_⟩
  intro I
  have hsrc := texprToThir_denoteScalarT (w := 32) (nIn := 0) []
      I qTexpr (fun _ => none) qTexpr_texprToThir
  have hfront := thirToJasmin_denote (w := 32) (nIn := 0) []
      I (Thir.ret (Atom.lit 8380417)) (LEnv.empty 32) (initFState 32 0)
      (inputValuation 32 0 I) c (initAgree I) hc
  have hspec := qTexpr_denoteScalarT I (fun _ => none)
  have hchain : some (BitVec.ofNat 32 8380417)
      = some (c.denote (inputValuation 32 0 I)) := by
    rw [← hspec, hsrc]; exact hfront
  exact (Option.some_inj.1 hchain).symm

/-! ## §4  The modular-arithmetic functions are outside the subset

Each of the seven ML-DSA modular-arithmetic literals is rejected by the typed
front. The theorems below are the machine-checked form of that statement; §5
isolates the operator heads responsible. -/

/-- `mod_q` is outside the typed front's subset, for either choice of which of
    its free names are parameters. -/
theorem modQTexpr_rejected : texprToThir ["a"] modQTexpr = none := rfl

/-- `mod_q` is rejected with `Q` supplied as a second parameter too. -/
theorem modQTexpr_rejected_with_Q : texprToThir ["a", "Q"] modQTexpr = none := rfl

/-- `add_mod_q` is outside the typed front's subset. -/
theorem addModQTexpr_rejected : texprToThir ["a", "b"] addModQTexpr = none := rfl

/-- `sub_mod_q` is outside the typed front's subset. -/
theorem subModQTexpr_rejected : texprToThir ["a", "b"] subModQTexpr = none := rfl

/-- `mul_mod_q` is outside the typed front's subset. -/
theorem mulModQTexpr_rejected : texprToThir ["a", "b"] mulModQTexpr = none := rfl

/-- `mod_pm` is outside the typed front's subset. -/
theorem modPmTexpr_rejected : texprToThir ["x", "alpha"] modPmTexpr = none := rfl

/-- `power2round` is outside the typed front's subset. -/
theorem power2roundTexpr_rejected : texprToThir ["r"] power2roundTexpr = none := rfl

/-- `mont_reduce` is outside the typed front's subset. -/
theorem montReduceTexpr_rejected : texprToThir ["a"] montReduceTexpr = none := rfl

/-! ## §5  The operator heads the typed front does not read

`mod_q` is the smallest ML-DSA function and its whole body is a single
`Rem` application, so the heads below locate the front's ML-DSA wall exactly.
`JasminBinOp` carries no remainder or division op, so the gap is at the dialect
and not only at the recogniser. -/

/-- The binary-ALU reader does not recognise the remainder head. -/
theorem recogBinTy_Rem : recogBinTy "Rem" = none := rfl

/-- The shift/rotate reader does not recognise the remainder head. -/
theorem recogShiftTy_Rem : recogShiftTy "Rem" = none := rfl

/-- The coercion reader does not recognise the remainder head. -/
theorem recogCastTy_Rem : recogCastTy "Rem" = false := rfl

/-- The binary-ALU reader does not recognise the division head. -/
theorem recogBinTy_Div : recogBinTy "Div" = none := rfl

/-- The binary-ALU reader does not recognise the signed-suffixed remainder head
    of `mod_pm`. -/
theorem recogBinTy_Rem_i32 : recogBinTy "Rem#i32" = none := rfl

/-- The coercion reader does not recognise the signed coercion head `cast#i32`,
    which `power2round` and `mont_reduce` carry. -/
theorem recogCastTy_cast_i32 : recogCastTy "cast#i32" = false := rfl

/-- The coercion reader does not recognise the named coercion head `cast#u32`. -/
theorem recogCastTy_cast_u32 : recogCastTy "cast#u32" = false := rfl

/-- The coercion reader does not recognise the signed coercion head `cast#i64`. -/
theorem recogCastTy_cast_i64 : recogCastTy "cast#i64" = false := rfl

/-- The width-suffixed coercion heads of `add_mod_q` — `cast#32` and `cast#64` —
    are recognised, so the coercion reader is not what rejects that literal. -/
theorem recogCastTy_cast_32_64 :
    recogCastTy "cast#32" = true ∧ recogCastTy "cast#64" = true := ⟨rfl, rfl⟩

/-- The `Add` head of `add_mod_q` is recognised, so the binary-ALU reader is not
    what rejects that literal either. -/
theorem recogBinTy_Add : recogBinTy "Add" = some .add := rfl

end CatCrypt.Crypto.SecureCompilation.CompileFromTExprMldsa
