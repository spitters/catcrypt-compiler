/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
import CatCrypt.Crypto.SecureCompilation.VIR.Core
import CatCrypt.Crypto.Primitives.Keccak

/-!
# The Keccak-f[1600] round (SHA-3) routed through `catCryptDialect` (scalar)

`Sha256RoundCatCryptEmit.lean` broadened the high algebraic crypto-SSA surface
`catCryptDialect` from the ChaCha20 quarter-round to the SHA-256 round-component
logical functions; `Chacha20BlockCatCryptEmit.lean` composes a committed
quarter-round `Com` into the whole block **structurally** (folding the per-QR
denote equality through the round structure, not a monolithic `rfl`). This file
applies the same recipe to the **Keccak-f[1600] permutation round** (FIPS 202
§3.2, the core of SHA-3 / SHAKE; HACL\*-benchmarked at `bench/keccak_compare/`).

A Keccak round over the 5×5 `BitVec 64` state is `θ → ρ → π → χ → ι`:

* **θ** (§3.2.1) — column parity `C[x] = ⊕_y A[x,y]`, the diffusion word
  `D[x] = C[x-1] ⊕ rotl(C[x+1], 1)`, and the lane update `A[x,y] ⊕ D[x]`.
  Op fragment: `bvXor`, `bvRol` (the `rotl …1`).
* **ρ** (§3.2.2) — per-lane left-rotate by the FIPS offset table: `bvRol n`.
* **π** (§3.2.3) — lane permutation. Pure index shuffle, no dialect op.
* **χ** (§3.2.4) — the only non-linear step, per lane
  `A[x,y] ⊕ ((¬A[x+1,y]) ∧ A[x+2,y])`. Op fragment: `andn` (the BMI1
  `(¬a) ∧ b` idiom, one op) and `bvXor`.
* **ι** (§3.2.5) — round-constant XOR into lane `(0,0)`: `bvConst` + `bvXor`.

## The op fragment

The catCrypt dialect carries these word ops natively (`CatCryptDialect.lean`):
`bvXor`, `bvRol` (denotes `BitVec.rotateLeft`, the FIPS ρ/θ rotates), `andn`
(`(~~~a) &&& b`, the χ idiom in one op), and `bvConst` (the ι round constant).
So each sub-step expresses *faithfully* as a straight-line `Com catCryptDialect`
program whose denotation is *definitionally* the FIPS reference — no opaque
`extCall` leaves.

Note on lowering: `bvRol` is denote-only in the `DialectToJasminCom` seam
(jasmin has no native scalar left-rotate); the seam-lowering path uses `bvRor`
with `64-n`. This file proves the *catCrypt denotation = FIPS spec* arm (the
`bvRol` form matches the spec's `rotateLeft` definitionally); the jasmin lowering
of the rotate steps is the `bvRor (64-n)` route already exercised by
`KeccakRotateSelect.lean`.

## Structure (NOT a monolithic 25-lane `Com`)

A single straight-line 25-lane `Com catCryptDialect` for the whole round is
hundreds of de-Bruijn-threaded ops, neither hand-authorable nor `rfl`-closable
at MCP heartbeats. Instead, mirroring `Chacha20BlockCatCryptEmit`:

1. Each *sub-step kernel* (`thetaColCat`, `thetaDCat`, `rhoLaneCat`, `chiLaneCat`,
   `iotaLaneCat`) is a small committed `Com catCryptDialect` program over the
   lanes it touches, proven to denote to its FIPS reference word function.
2. The round-level steps (`thetaCat`, `rhoCat`, `piCat`, `chiCat`, `iotaCat`)
   are `KState → KState` functions driven by those committed `Com` denotations,
   each proven equal to its `Primitives.Keccak` counterpart.
3. `keccakRoundCat` composes them as `ι ∘ χ ∘ π ∘ ρ ∘ θ`; the keystone
   `keccakRound_catcrypt_eq` folds the per-step equalities through the round
   structure — NOT one monolithic `rfl`.

0 sorries.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundCatCryptEmit

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.Primitives.Keccak

/-! ## 1. The dialect word type and per-op peel lemmas -/

/-- The 64-bit machine-word dialect type (a Keccak lane). -/
abbrev T64 : CryptoTy := .sword 64

/-- `bvXor` waist (64-bit). -/
def kXorW (a b : BitVec 64) : BitVec 64 := a ^^^ b
/-- `andn` waist: `(~~~a) &&& b` (the χ idiom). -/
def kAndnW (a b : BitVec 64) : BitVec 64 := (~~~a) &&& b
/-- `bvRol` waist: rotate-left by the immediate `n`. -/
def kRolW (n : Nat) (a : BitVec 64) : BitVec 64 := a.rotateLeft n
/-- `bvConst` waist. -/
def kConstW (v : BitVec 64) : BitVec 64 := v

/-- Peel one `bvXor 64` binding. -/
theorem denote_var_bvXor {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (kXorW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `andn 64` binding. -/
theorem denote_var_andn {Γ : Ctxt catCryptDialect} {s : CryptoTy}
    (va vb : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.andn 64) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (kAndnW (va.lookup V) (vb.lookup V))) := rfl

/-- Peel one `bvRol 64 n` binding. -/
theorem denote_var_bvRol {Γ : Ctxt catCryptDialect} {n : Nat} {s : CryptoTy}
    (va : Ctxt.Var Γ (CryptoTy.sword 64))
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvRol 64 n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (kRolW n (va.lookup V))) := rfl

/-- Peel one `bvConst 64 v` binding. -/
theorem denote_var_bvConst {Γ : Ctxt catCryptDialect} {v : BitVec 64} {s : CryptoTy}
    (body : Com catCryptDialect (CryptoTy.sword 64 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (CatCryptOp.bvConst 64 v) rfl .nil) body).denote V
      = body.denote (V.extend (kConstW v)) := rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-- `Ctxt.Var.here.lookup` on a cons valuation reads the head. -/
@[simp] theorem lookup_here_cons {Γ : Ctxt catCryptDialect} {t : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (HVector.cons v V) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on a cons valuation skips the head. -/
@[simp] theorem lookup_there_cons {Γ : Ctxt catCryptDialect} {t t' : CryptoTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (HVector.cons v V) = w.lookup V := rfl

/-! ## 2. Input valuations -/

/-- A single-lane input valuation. -/
abbrev inV1 (a : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) [T64] :=
  HVector.cons a HVector.nil

/-- A two-lane input valuation. -/
abbrev inV2 (a b : BitVec 64) : Ctxt.Valuation (d := catCryptDialect) [T64, T64] :=
  HVector.cons a (HVector.cons b HVector.nil)

/-- A three-lane input valuation. -/
abbrev inV3 (a b c : BitVec 64) :
    Ctxt.Valuation (d := catCryptDialect) [T64, T64, T64] :=
  HVector.cons a (HVector.cons b (HVector.cons c HVector.nil))

/-- A five-lane input valuation (a θ column). -/
abbrev inV5 (a b c d e : BitVec 64) :
    Ctxt.Valuation (d := catCryptDialect) [T64, T64, T64, T64, T64] :=
  HVector.cons a (HVector.cons b (HVector.cons c
    (HVector.cons d (HVector.cons e HVector.nil))))

set_option maxHeartbeats 1000000

/-! ## 3. θ: column parity, diffusion word, lane update

`θ` (FIPS 202 §3.2.1): `C[x] = ⊕_y A[x,y]`, `D[x] = C[x-1] ⊕ rotl(C[x+1],1)`,
`A'[x,y] = A[x,y] ⊕ D[x]`. -/

/-- **θ column parity** over `catCryptDialect`, input the five lanes of a column
    `[a0,a1,a2,a3,a4]`: `a0 ^ a1 ^ a2 ^ a3 ^ a4` (four `bvXor`). -/
def thetaColCat : Com catCryptDialect [T64, T64, T64, T64, T64] T64 :=
  -- t1 = a0 ^ a1 ;  ctx [a0,a1,a2,a3,a4]
  Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  -- t2 = t1 ^ a2 ;  t1 = here, a2 = there³ here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons .here (.cons (.there (.there (.there .here))) .nil)))
  -- t3 = t2 ^ a3 ;  t2 = here, a3 = there⁵ here (a3 was there³, shifted by 2)
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) .nil)))
  -- out = t3 ^ a4 ;  t3 = here, a4 = there⁷ here (a4 was there⁴, shifted by 3)
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl
      (.cons .here
        (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)))
  (Com.ret .here))))

/-- **θ diffusion word** over `catCryptDialect`, input `[cm, cp]` for
    `cm = C[x-1]`, `cp = C[x+1]`: `cm ^ rotl(cp, 1)` (one `bvRol 1`, one `bvXor`). -/
def thetaDCat : Com catCryptDialect [T64, T64] T64 :=
  -- r = rotl cp 1 ;  ctx [cm, cp],  cp = there here
  Com.var (Expr.mk (CatCryptOp.bvRol 64 1) rfl (.cons (.there .here) .nil))
  -- out = cm ^ r ;  cm = there here, r = here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (Com.ret .here))

/-- **θ lane update** over `catCryptDialect`, input `[a, d]`: `a ^ d` (one `bvXor`). -/
def thetaLaneCat : Com catCryptDialect [T64, T64] T64 :=
  Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons .here (.cons (.there .here) .nil)))
  (Com.ret .here)

/-- The catCrypt column parity computes `a0 ^ a1 ^ a2 ^ a3 ^ a4`. -/
theorem thetaCol_catcrypt_denote (a0 a1 a2 a3 a4 : BitVec 64) :
    thetaColCat.denote (inV5 a0 a1 a2 a3 a4) = a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 := by
  simp only [thetaColCat]
  rw [denote_var_bvXor, denote_var_bvXor, denote_var_bvXor, denote_var_bvXor]
  simp only [Com.denote, lookup_here_extend, lookup_there_extend, kXorW]
  rfl

/-- The catCrypt θ diffusion word computes `cm ^ rotl(cp, 1)`. -/
theorem thetaD_catcrypt_denote (cm cp : BitVec 64) :
    thetaDCat.denote (inV2 cm cp) = cm ^^^ cp.rotateLeft 1 := rfl

/-- The catCrypt θ lane update computes `a ^ d`. -/
theorem thetaLane_catcrypt_denote (a d : BitVec 64) :
    thetaLaneCat.denote (inV2 a d) = a ^^^ d := rfl

/-! ## 4. ρ: per-lane left-rotate -/

/-- **ρ lane rotate** over `catCryptDialect`, input `[a]` and the immediate offset
    `n`: `rotl(a, n)` (one `bvRol n`). -/
def rhoLaneCat (n : Nat) : Com catCryptDialect [T64] T64 :=
  Com.var (Expr.mk (CatCryptOp.bvRol 64 n) rfl (.cons .here .nil))
  (Com.ret .here)

/-- The catCrypt ρ lane rotate computes `rotl(a, n)`. -/
theorem rhoLane_catcrypt_denote (n : Nat) (a : BitVec 64) :
    (rhoLaneCat n).denote (inV1 a) = a.rotateLeft n := rfl

/-! ## 5. χ: per-lane nonlinear mixing -/

/-- **χ lane** over `catCryptDialect`, input `[a, a1, a2]`:
    `a ^ ((¬a1) ∧ a2)` (one `andn`, one `bvXor`). -/
def chiLaneCat : Com catCryptDialect [T64, T64, T64] T64 :=
  -- q = andn a1 a2 (= ¬a1 & a2) ;  ctx [a,a1,a2],  a1 = there here, a2 = there² here
  Com.var (Expr.mk (CatCryptOp.andn 64) rfl
      (.cons (.there .here) (.cons (.there (.there .here)) .nil)))
  -- out = a ^ q ;  a = there here, q = here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (Com.ret .here))

/-- The catCrypt χ lane computes `a ^ ((¬a1) ∧ a2)`. -/
theorem chiLane_catcrypt_denote (a a1 a2 : BitVec 64) :
    chiLaneCat.denote (inV3 a a1 a2) = a ^^^ (~~~a1 &&& a2) := rfl

/-! ## 6. ι: round-constant XOR into lane (0,0) -/

/-- **ι lane** over `catCryptDialect`, input `[a]` and the round constant `rc`:
    `a ^ rc` (one `bvConst rc`, one `bvXor`). -/
def iotaLaneCat (rc : BitVec 64) : Com catCryptDialect [T64] T64 :=
  -- k = const rc ;  ctx [a]
  Com.var (Expr.mk (CatCryptOp.bvConst 64 rc) rfl .nil)
  -- out = a ^ k ;  a = there here, k = here
  (Com.var (Expr.mk (CatCryptOp.bvXor 64) rfl (.cons (.there .here) (.cons .here .nil)))
  (Com.ret .here))

/-- The catCrypt ι lane computes `a ^ rc`. -/
theorem iotaLane_catcrypt_denote (rc a : BitVec 64) :
    (iotaLaneCat rc).denote (inV1 a) = a ^^^ rc := rfl

/-! ## 7. Round-level steps driven by the committed `Com` denotations

Each step is `KState → KState`, with the arithmetic computed by the committed
`Com catCryptDialect` sub-step program; the `_eq` lemma rewrites it to the
`Primitives.Keccak` reference. The index sets / permutations are *identical* to
the FIPS spec — only the per-lane arithmetic is replaced by the dialect `Com`. -/

/-- θ over the catCrypt sub-step `Com`s. The column parities and diffusion words
    are computed by `thetaColCat` / `thetaDCat`, the lane update by
    `thetaLaneCat`. -/
def thetaCat (a : KState) : KState :=
  let c : Fin 5 → BitVec 64 := fun x =>
    thetaColCat.denote (inV5 (a x 0) (a x 1) (a x 2) (a x 3) (a x 4))
  let d : Fin 5 → BitVec 64 := fun x =>
    thetaDCat.denote (inV2 (c ⟨(x.val + 4) % 5, by omega⟩) (c ⟨(x.val + 1) % 5, by omega⟩))
  fun x y => thetaLaneCat.denote (inV2 (a x y) (d x))

/-- ρ over the catCrypt sub-step `Com`. -/
def rhoCat (a : KState) : KState := fun x y =>
  (rhoLaneCat (rotOffset x y)).denote (inV1 (a x y))

/-- π over the catCrypt steps: a pure index permutation (no dialect op). Identical
    to `Primitives.Keccak.pi`. -/
def piCat (a : KState) : KState := fun x y =>
  a ⟨(x.val + 3 * y.val) % 5, by omega⟩ x

/-- χ over the catCrypt sub-step `Com`. -/
def chiCat (a : KState) : KState := fun x y =>
  chiLaneCat.denote (inV3 (a x y)
    (a ⟨(x.val + 1) % 5, by omega⟩ y) (a ⟨(x.val + 2) % 5, by omega⟩ y))

/-- ι over the catCrypt sub-step `Com`. -/
def iotaCat (a : KState) (rc : BitVec 64) : KState := fun x y =>
  if x.val == 0 && y.val == 0 then (iotaLaneCat rc).denote (inV1 (a x y)) else a x y

/-- **θ equals the FIPS reference.** -/
theorem thetaCat_eq (a : KState) : thetaCat a = theta a := by
  funext x y
  simp only [thetaCat, theta, thetaCol_catcrypt_denote, thetaD_catcrypt_denote,
    thetaLane_catcrypt_denote]

/-- **ρ equals the FIPS reference.** -/
theorem rhoCat_eq (a : KState) : rhoCat a = rho a := by
  funext x y
  simp only [rhoCat, rho, rhoLane_catcrypt_denote]

/-- **π equals the FIPS reference** (definitionally — same index permutation). -/
theorem piCat_eq (a : KState) : piCat a = pi a := by
  funext x y
  simp only [piCat, pi]

/-- **χ equals the FIPS reference.** -/
theorem chiCat_eq (a : KState) : chiCat a = chi a := by
  funext x y
  simp only [chiCat, chi, chiLane_catcrypt_denote]

/-- **ι equals the FIPS reference.** -/
theorem iotaCat_eq (a : KState) (rc : BitVec 64) : iotaCat a rc = iota a rc := by
  funext x y
  simp only [iotaCat, iota, iotaLane_catcrypt_denote]

/-! ## 8. The whole round, composed structurally

`keccakRoundCat = ι ∘ χ ∘ π ∘ ρ ∘ θ`, each step the committed catCrypt `Com`.
The keystone `keccakRound_catcrypt_eq` folds the five per-step `_eq` lemmas
through the composition (NOT a monolithic `rfl` over the whole 25-lane round). -/

/-- One Keccak round over the committed catCrypt-dialect sub-step `Com`s:
    `ι (χ (π (ρ (θ a)))) rc`. -/
def keccakRoundCat (a : KState) (rc : BitVec 64) : KState :=
  iotaCat (chiCat (piCat (rhoCat (thetaCat a)))) rc

/-- **Keystone: the whole catCrypt round equals the FIPS-202 reference round.**
    Every per-lane word operation in the round (the θ XOR/rotate diffusion, the ρ
    rotates, the χ `andn`/XOR mixing, the ι round-constant XOR) is computed by a
    committed `Com catCryptDialect` program, so the whole benchmarked Keccak round
    primitive routes through the high `catCryptDialect` surface. Proved by folding
    the five per-step equalities through the composition, not a monolithic `rfl`. -/
theorem keccakRound_catcrypt_eq (a : KState) (rc : BitVec 64) :
    keccakRoundCat a rc = keccakRound a rc := by
  simp only [keccakRoundCat, keccakRound, thetaCat_eq, rhoCat_eq, piCat_eq,
    chiCat_eq, iotaCat_eq]

end CatCrypt.Crypto.SecureCompilation.VIR.KeccakRoundCatCryptEmit
