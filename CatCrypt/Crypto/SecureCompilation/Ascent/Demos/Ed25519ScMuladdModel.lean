/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519SymExec
public import CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped

/-!
# The `ed25519_sc_muladd` word model and its part maps

`muladdModel k a r` is the schoolbook product `r + k · a` on eight 64-bit words followed by
the Barrett reduction `reduceModel` of `Ed25519SymExec`. The word model and its
correctness statement are those of `CatCrypt.Crypto.EdDSA.Ed25519ScalarEmit`
(`muladdModel`, `muladdModel_val`), from which the machine code is compiled; the compiler
package does not depend on that module, so they are restated here.

`muladdG` produces the single-assignment word statements of the model over numbered slots:
the nine constant slots of `constStmts`, the multiply-accumulate sweep of the product, and
then the four phases of the reduction. `muladdG_val` states that the result handles denote
`muladdModel`.

The entry map `scmIn` and the maps `scmMap1` … `scmMap8` between the nine parts of the
imported block are the arguments of the part checks. The checks themselves are
`decide +kernel` and live in `Ed25519ScMuladdShippedProof`; keeping the model and the maps
here lets the part-check statements be evaluated, and other modules use the model, without
elaborating the checks.

## Main results

* `muladdModel_val`: the word model computes `(r + k · a) mod L`.
* `muladdG_val`: the result handles of the generated statements denote `muladdModel`.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
set_option exponentiation.threshold 600

namespace CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMemDerived
open CatCrypt.Crypto.SecureCompilation.Ascent.Imported.Ed25519ScMuladdShipped
open CatCrypt.Crypto.SecureCompilation.MultiLimbKernel
open CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScReduceShippedProof
open CatCrypt.Util (Ed25519L ed25519L_eq)

/-! ## 1. The word model -/

/-- The multiply-add `r + k · a` followed by the Barrett reduction, on the word model. -/
def muladdModel (k a r : List (BitVec 64)) : List (BitVec 64) := reduceModel (mulRows k a r)

/-- The multiply-add model computes `(r + k · a) mod L`. -/
theorem muladdModel_val (k a r : List (BitVec 64)) (hk : k.length = 4) (ha : a.length = 4)
    (hr : r.length = 4) :
    bignumVal (muladdModel k a r) = (bignumVal r + bignumVal k * bignumVal a) % Ed25519L := by
  simp only [muladdModel]
  rw [reduceModel_val _ (by rw [mulRows_length _ _ _ (by omega)]; omega),
    mulRows_val _ _ _ (by omega) (by omega)]

/-! ## 2. The statement generator -/

/-- The generator of `muladdModel` over three times four input handles: the constant slots
    `n .. n + 8`, then the product from slot `n + 9`, then the reduction. -/
def muladdG (k a r : List WE) (n : Nat) : List WE × List WE :=
  let r0 := mulRowsG k a r (n + 9)
  let m0 := n + 9 + r0.1.length
  let r1 := mulRowsG r0.2 (slotsFrom n 5) (List.replicate 5 (.lit 0)) m0
  let m1 := m0 + r1.1.length
  let r2 := mulRowsG (r1.2.drop 8) (slotsFrom (n + 5) 4) (List.replicate 4 (.lit 0)) m1
  let m2 := m1 + r2.1.length
  let r3 := addLimbsG (r0.2.take 4) ((r2.2.take 4).map notW) (.lit 1) m2
  let m3 := m2 + r3.1.length
  let r4 := condSubG r3.2.dropLast (slotsFrom (n + 5) 4) m3
  (constStmts ++ (r0.1 ++ (r1.1 ++ (r2.1 ++ (r3.1 ++ r4.1)))), r4.2)

theorem muladdG_val (ρ : Nat → BitVec 64) (k a r : List WE) (n : Nat)
    (h : Holds ρ n (muladdG k a r n).1) :
    (muladdG k a r n).2.map (WE.eval ρ)
      = muladdModel (k.map (WE.eval ρ)) (a.map (WE.eval ρ)) (r.map (WE.eval ρ)) := by
  simp only [muladdG, muladdModel] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨hc, h0, h1, h2, h3, h4⟩ := h
  rw [constStmts_length] at h0 h1 h2 h3 h4
  obtain ⟨hmu, hp⟩ := constStmts_eval ρ n hc
  rw [condSubG_val ρ _ _ _ h4, hp, List.map_dropLast, addLimbsG_val ρ _ _ _ _ h3,
    notW_map, List.map_take, List.map_take, mulRowsG_val ρ _ _ _ _ h2, List.map_drop,
    mulRowsG_val ρ _ _ _ _ h1, hmu, hp, zeros_eval, zeros_eval,
    mulRowsG_val ρ _ _ _ _ h0]
  rfl

/-! ## 3. The nine parts of `ed25519_sc_muladd` -/

/-- The statements of the multiply-add over the input slots `0 .. 11`, from slot `16`. -/
def mStmts : List WE := (muladdG (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16).1

/-- The four result handles of the multiply-add. -/
def mOuts : List WE := (muladdG (slotsFrom 0 4) (slotsFrom 4 4) (slotsFrom 8 4) 16).2

/-- The statements of slots `a .. b - 1`. -/
def mSlice (a b : Nat) : List WE := (mStmts.drop (a - 16)).take (b - a)

/-- The twelve input limbs: cell `(%rsi, 8k)` holds slot `k`, cell `(%rdx, 8k)` slot
    `4 + k`, and cell `(%rcx, 8k)` slot `8 + k`. -/
def scmIn : List (Loc × WE) :=
  (List.range 4).map (fun k => (Loc.cell "%rsi" ((8 * k : Nat) : Int), WE.v k)) ++
  (List.range 4).map (fun k => (Loc.cell "%rdx" ((8 * k : Nat) : Int), WE.v (4 + k))) ++
  (List.range 4).map (fun k => (Loc.cell "%rcx" ((8 * k : Nat) : Int), WE.v (8 + k)))

/-- The four output limbs: cell `(%rdi, 8i)` holds slot `430 + i`. -/
def scmOut : List (Loc × WE) := [dk 0 430, dk 8 431, dk 16 432, dk 24 433]

/-- The stack cells holding the loop indices. -/
def scmIdx : List (Loc × WE) :=
  [sk 168 (.lit 3), sk 160 (.lit 2), sk 152 (.lit 1), sk 144 (.lit 0)]

/-- The stack cells holding the four limbs of `L`, the constant slots `21 .. 24`. -/
def scmL : List (Loc × WE) :=
  [sk 104 (.v 24), sk 112 (.v 23), sk 120 (.v 22), sk 128 (.v 21)]

/-- The stack cells holding the five limbs of the Barrett constant, the constant slots
    `16 .. 20`. -/
def scmMu : List (Loc × WE) :=
  [sk 40 (.v 20), sk 32 (.v 19), sk 24 (.v 18), sk 16 (.v 17), sk 8 (.v 16)]

/-- The locations after part 1. -/
def scmMap1 : List (Loc × WE) :=
  [rg "%rbx" (.v 67), rg "%rsi" (.v 66), rg "%rcx" (.v 65), rg "%rax" (.v 64),
    rg "%r9" (.v 63), rg "%r10" (.v 58), rg "%r12" (.v 53),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28), sk 128 (.v 7), sk 112 (.v 6),
    sk 104 (.v 5), sk 88 (.v 4), sk 120 (.v 3), sk 80 (.v 2)] ++ scmIdx

/-- The locations after part 2. The constant slot `19` is the all-ones word. -/
def scmMap2 : List (Loc × WE) :=
  [rg "%rax" (.and (.xor (.lit 0) (.v 112)) (notW (.v 113))),
    rg "%r8" (.and (.lit 0) (.v 112)),
    rg "%rbp" (.add (.v 111) (cw (.v 112) (.v 109) (.v 110))),
    rg "%rbx" (.v 113),
    rg "%rcx" (.add (.v 101) (cw (.v 102) (.v 99) (.v 100)))] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 3. -/
def scmMap3 : List (Loc × WE) :=
  [rg "%rsi" (.v 164), rg "%r11" (.v 163), rg "%rax" (.v 154), rg "%r8" (.v 153),
    rg "%r9" (.v 148)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 4. -/
def scmMap4 : List (Loc × WE) :=
  [rg "%rcx" (.v 218), rg "%rbp" (.v 217), rg "%rdi" (.v 216), rg "%rsi" (.v 215),
    rg "%rbx" (.v 214), rg "%r11" (.v 213), rg "%rax" (.v 204), rg "%r8" (.v 203),
    rg "%r9" (.v 198)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 48 (.v 98), sk 0 (.v 93), sk 88 (.v 88),
    sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 5. -/
def scmMap5 : List (Loc × WE) :=
  [rg "%rcx" (.v 266), rg "%rbx" (cw (.v 267) (.v 264) (.v 265)), rg "%r10" (.v 268),
    rg "%rbp" (.v 267), rg "%r11" (.v 263), rg "%rax" (.v 254), rg "%r8" (.v 253),
    rg "%r9" (.v 248)] ++ scmL ++ scmMu ++
  [sk 80 (.v 104), sk 56 (.v 103), sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48),
    sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 6. -/
def scmMap6 : List (Loc × WE) :=
  [rg "%rbp" (.v 317), rg "%rbx" (.lit 0), rg "%rdi" (.and (.lit 0) (.v 317)),
    rg "%rax" (.add (.v 316) (cw (.v 317) (.v 314) (.v 315))), rg "%rsi" (.v 318),
    rg "%rcx" (.v 313), rg "%r9" (.v 298), rg "%r10" (.v 293), rg "%r11" (.v 288),
    sk 80 (.v 308), sk 56 (.v 304), sk 40 (.v 303)] ++ scmL ++
  [sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 7. -/
def scmMap7 : List (Loc × WE) :=
  [rg "%rsi" (.xor (.and (.v 353) (.v 367)) (.and (.xor (.v 353) (.v 367)) (notW (.v 368)))),
    rg "%rdi" (.add (.v 366) (cw (.v 367) (.lit 0) (.v 365))),
    rg "%rax" (.v 364), rg "%r9" (.v 363), rg "%r11" (.v 358), rg "%rbp" (.v 348),
    sk 32 (.v 368), sk 48 (.v 328), sk 80 (.v 308), sk 56 (.v 304), sk 40 (.v 303)] ++
  scmL ++ [sk 88 (.v 88), sk 72 (.v 68), sk 64 (.v 48), sk 96 (.v 28)] ++ scmIdx

/-- The locations after part 8. -/
def scmMap8 : List (Loc × WE) :=
  [rg "%r9" (.xor (.v 88) (notW (.v 368))), rg "%rcx" (.and (.v 88) (notW (.v 368))),
    rg "%rbp" (.v 415), rg "%rsi" (.v 414), rg "%rbx" (.v 413), rg "%r8" (.v 412),
    rg "%rdi" (.v 409), rg "%rax" (.v 406)] ++ scmL ++ scmIdx

end CatCrypt.Crypto.SecureCompilation.Ascent.Demos.Ed25519ScMuladdShippedProof
