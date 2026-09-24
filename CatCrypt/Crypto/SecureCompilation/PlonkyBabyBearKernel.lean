/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.MulModKernel
public import CatCrypt.Crypto.SecureCompilation.AddModKernel

/-!
# Routing plonky3's BabyBear field through the compiler

plonky3's prime field is BabyBear, `p = 2^31 - 2^27 + 1`, a 31-bit prime — so its
add/mul fit the single-limb field kernels (`p < 2^32`) directly. Instantiating those
kernels at the BabyBear prime gives BabyBear field arithmetic compiled through the
`Com → RegProg → {AArch64, RISC-V}` pipeline, value-correct against `ZMod p`. This is
the field layer of plonky3 routed through the verified compiler.
-/

@[expose] public section

namespace CatCrypt.Crypto.SecureCompilation.PlonkyBabyBearKernel

open CatCrypt.Crypto.SecureCompilation.ScalarLin
open CatCrypt.Crypto.SecureCompilation.MulModKernel
open CatCrypt.Crypto.SecureCompilation.AddModKernel

/-- The BabyBear prime `2^31 - 2^27 + 1`. -/
def babyBear : Nat := 2013265921

theorem babyBear_pos : 1 < babyBear := by decide
theorem babyBear_lt : babyBear < 2 ^ 32 := by decide

instance : NeZero babyBear := ⟨by decide⟩

/-- BabyBear field multiplication, compiled through the scalar pipeline. -/
def bbMulProg : RegProg := mulmodProg babyBear

/-- BabyBear field addition, compiled through the scalar pipeline. -/
def bbAddProg : RegProg := addmodProg babyBear

/-- **BabyBear multiply is value-correct.** -/
theorem bbMul_correct (env : Env)
    (ha : (env "a").toNat < babyBear) (hb : (env "b").toNat < babyBear) :
    ((RegProg.denotePure bbMulProg env) "res").toNat
      = ((env "a").toNat * (env "b").toNat) % babyBear :=
  mulmodProg_toNat babyBear env babyBear_pos babyBear_lt ha hb

/-- …and computes the `ZMod babyBear` field product. -/
theorem bbMul_zmod (env : Env)
    (ha : (env "a").toNat < babyBear) (hb : (env "b").toNat < babyBear) :
    ((RegProg.denotePure bbMulProg env) "res").toNat
      = (((env "a").toNat : ZMod babyBear) * ((env "b").toNat : ZMod babyBear)).val :=
  mulmodProg_zmod babyBear env babyBear_pos babyBear_lt ha hb

/-- **BabyBear addition is value-correct.** -/
theorem bbAdd_correct (env : Env)
    (ha : (env "a").toNat < babyBear) (hb : (env "b").toNat < babyBear) :
    ((RegProg.denotePure bbAddProg env) "res").toNat
      = ((env "a").toNat + (env "b").toNat) % babyBear :=
  addmodProg_toNat babyBear env (by decide) (by decide) ha hb

end CatCrypt.Crypto.SecureCompilation.PlonkyBabyBearKernel
