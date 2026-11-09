/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public meta import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian
public import CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveLoweringJacobian
public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFrontJac

/-!
# Compiled bytes of the Jacobian addition and doubling over BabyBear

Each coordinate of the `add-2007-bl` addition `jacAddOps` and of the `dbl-2007-bl` doubling
`jacDblOps` of Jacobian triples over BabyBear, `p = 2013265921`, is a Lean function of the
coordinates, which `reifyField%` reads, with the formula unfolded, as a literal over its
parameters. The curve coefficient `a` of the doubling is its fourth scalar parameter, so that
one compiled program serves every curve over the field.

## Main results

* `addXAbi_bytes`, `dblAbi_bytes` — for every modulus `p < 2 ^ 64`, every result of `compileA` on a
  typed literal under the six-scalar layout `addXAbi`, respectively the four-scalar layout
  `dblAbi`, whose erasure has an ascent result under `hax64WExit`, computes that function of
  the argument registers.
* `jacAddY_fnCorres`, `jacAddZ_fnCorres`, `jacDblX_fnCorres`, `jacDblY_fnCorres`,
  `jacDblZ_fnCorres` — each literal denotes its coordinate under `hax64WExit`.
* `jacAdd_bytes`, `jacDbl_bytes` — for every coordinate `i`, every result of `compileA` on the
  typed literal of coordinate `i` computes coordinate `i` of `jacAddOps`, respectively of
  `jacDblOps`, of the argument registers. That `compileA` accepts the literals is measured
  outside Lean, by the executables' row harness.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.EllipticCurveDialect (jacAddOps jacDblOps coord)
open _root_.Hax (TExpr ImpExpr)
open _root_.Hax.Ascent (FnCorres enc bindParams)
open CatCrypt.Crypto.Hax (hax64WExit spineLamFree)
open CatCrypt.Hax.ReifyField (enc_zmod)
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## The layouts -/

/-- The layout of a coordinate of the doubling: the coordinates `x`, `y`, `z` and the curve
    coefficient `a` in `%rdi`, `%rsi`, `%rdx`, `%rcx`, no constant, the scalar result in
    `%rax`, the frame of `compileA`. -/
def dblAbi : AbiLayout :=
  AbiLayout.mk [⟨"x", "%rdi", .scalar⟩, ⟨"y", "%rsi", .scalar⟩, ⟨"z", "%rdx", .scalar⟩,
    ⟨"a", "%rcx", .scalar⟩] [] (.reg "%rax") [] (-256) (-8) [] []

/-- The types of the parameters of `dblAbi`: each a `u64` word. -/
def dblTypes : List (String × _root_.Hax.ImpType) :=
  dblAbi.args.map fun a => (a.name, .uint .w64)

/-- **Compiled bytes under the six-scalar layout.** If `compileA` returns `(P, bytes)` on `te`
    under `addXAbi`, the statement spine of `te.erase` binds no closure, and `te.erase` from
    the environment binding `x1`, `y1`, `z1`, `x2`, `y2`, `z2` returns the encoding of `f a`
    under `hax64WExit`, then from every entry state whose six argument registers hold the
    canonical representatives of the coordinates of `a`, the bytes decode to a program that
    halts in a state whose `%rax` reads back the encoding of `f a`. -/
theorem addXAbi_bytes {p : ℕ} (hp : p < 2 ^ 64) (te : TExpr) (fname : String) {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA te addXAbi fname = some (P, bytes))
    (hsp : spineLamFree te.erase = true)
    (f : ZMod p × ZMod p × ZMod p × ZMod p × ZMod p × ZMod p × Unit → ZMod p)
    (hf : FnCorres hax64WExit te.erase
      (fun a => bindParams [("x1", enc a.1), ("y1", enc a.2.1), ("z1", enc a.2.2.1),
        ("x2", enc a.2.2.2.1), ("y2", enc a.2.2.2.2.1), ("z2", enc a.2.2.2.2.2.1)])
      (fun _ => True) f)
    (sa : AState) (a : ZMod p × ZMod p × ZMod p × ZMod p × ZMod p × ZMod p × Unit)
    (h1 : a.1.val = (sa.regs "%rdi").toNat) (h2 : a.2.1.val = (sa.regs "%rsi").toNat)
    (h3 : a.2.2.1.val = (sa.regs "%rdx").toNat) (h4 : a.2.2.2.1.val = (sa.regs "%rcx").toNat)
    (h5 : a.2.2.2.2.1.val = (sa.regs "%r8").toNat)
    (h6 : a.2.2.2.2.2.1.val = (sa.regs "%r9").toNat) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ addXAbi.ResultOf sa sa' (enc (f a)) := by
  refine leanFront_correct_scalar te addXAbi fname _ _ hc hsp _ _ _ hf (by simp [addXAbi]) rfl
    (by decide) sa ?_ a trivial ?_
  · have hr : addXAbi.regions = [] := rfl
    refine ⟨by simp [addXAbi], ?_, ?_,
      AbiLayout.stackIn_of_regCarriedB (by decide) sa⟩ <;> simp [hr]
  · simp [addXAbi, enc_zmod hp, h1, h2, h3, h4, h5, h6]

/-- **Compiled bytes under the four-scalar layout.** If `compileA` returns `(P, bytes)` on `te`
    under `dblAbi`, the statement spine of `te.erase` binds no closure, and `te.erase` from
    the environment binding `x`, `y`, `z`, `a` returns the encoding of `f a` under
    `hax64WExit`, then from every entry state whose four argument registers hold the canonical
    representatives of the components of `a`, the bytes decode to a program that halts in a
    state whose `%rax` reads back the encoding of `f a`. -/
theorem dblAbi_bytes {p : ℕ} (hp : p < 2 ^ 64) (te : TExpr) (fname : String) {P : Lprog}
    {bytes : List (BitVec 8)} (hc : compileA te dblAbi fname = some (P, bytes))
    (hsp : spineLamFree te.erase = true)
    (f : ZMod p × ZMod p × ZMod p × ZMod p × Unit → ZMod p)
    (hf : FnCorres hax64WExit te.erase
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1), ("z", enc a.2.2.1),
        ("a", enc a.2.2.2.1)])
      (fun _ => True) f)
    (sa : AState) (a : ZMod p × ZMod p × ZMod p × ZMod p × Unit)
    (h1 : a.1.val = (sa.regs "%rdi").toNat) (h2 : a.2.1.val = (sa.regs "%rsi").toNat)
    (h3 : a.2.2.1.val = (sa.regs "%rdx").toNat)
    (h4 : a.2.2.2.1.val = (sa.regs "%rcx").toNat) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ dblAbi.ResultOf sa sa' (enc (f a)) := by
  refine leanFront_correct_scalar te dblAbi fname _ _ hc hsp _ _ _ hf (by simp [dblAbi]) rfl
    (by decide) sa ?_ a trivial ?_
  · have hr : dblAbi.regions = [] := rfl
    refine ⟨by simp [dblAbi], ?_, ?_,
      AbiLayout.stackIn_of_regCarriedB (by decide) sa⟩ <;> simp [hr]
  · simp [dblAbi, enc_zmod hp, h1, h2, h3, h4]

/-! ## The addition over BabyBear -/

/-- The `Y` coordinate of the Jacobian sum of `(x1, y1, z1)` and `(x2, y2, z2)` over
    BabyBear. -/
def jacAddYLean (x1 y1 z1 x2 y2 z2 : ZMod 2013265921) : ZMod 2013265921 :=
  (jacAddOps (x1, y1, z1) (x2, y2, z2)).2.1

/-- The `Z` coordinate of the Jacobian sum of `(x1, y1, z1)` and `(x2, y2, z2)` over
    BabyBear. -/
def jacAddZLean (x1 y1 z1 x2 y2 z2 : ZMod 2013265921) : ZMod 2013265921 :=
  (jacAddOps (x1, y1, z1) (x2, y2, z2)).2.2

/-- The literal of `jacAddYLean`, with `jacAddOps` unfolded. -/
def jacAddYImp : ImpExpr := reifyField% jacAddYLean unfolding jacAddOps

/-- The literal of `jacAddZLean`, with `jacAddOps` unfolded. -/
def jacAddZImp : ImpExpr := reifyField% jacAddZLean unfolding jacAddOps

theorem jacAddYImp_toTExpr_isSome : (jacAddYImp.toTExpr addXTypes).isSome = true := by
  rfl

theorem jacAddZImp_toTExpr_isSome : (jacAddZImp.toTExpr addXTypes).isSome = true := by
  rfl

/-- The typed literal of `jacAddYLean`, the six parameters typed as `u64` words. -/
def jacAddYT : TExpr := (jacAddYImp.toTExpr addXTypes).get jacAddYImp_toTExpr_isSome

/-- The typed literal of `jacAddZLean`, the six parameters typed as `u64` words. -/
def jacAddZT : TExpr := (jacAddZImp.toTExpr addXTypes).get jacAddZImp_toTExpr_isSome

theorem jacAddYT_erase : jacAddYT.erase = jacAddYImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacAddYImp_toTExpr_isSome).symm

theorem jacAddZT_erase : jacAddZT.erase = jacAddZImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacAddZImp_toTExpr_isSome).symm

/-- From the entry environment binding the six coordinates, the literal `jacAddYImp` returns
    the encoding of `jacAddYLean` under the table `hax64WExit`. -/
theorem jacAddY_fnCorres :
    FnCorres hax64WExit jacAddYImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 ×
        ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x1", enc a.1), ("y1", enc a.2.1), ("z1", enc a.2.2.1),
        ("x2", enc a.2.2.2.1), ("y2", enc a.2.2.2.2.1), ("z2", enc a.2.2.2.2.2.1)])
      (fun _ => True)
      (fun a => jacAddYLean a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1) := by
  ascend_reified jacAddYLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

/-- From the entry environment binding the six coordinates, the literal `jacAddZImp` returns
    the encoding of `jacAddZLean` under the table `hax64WExit`. -/
theorem jacAddZ_fnCorres :
    FnCorres hax64WExit jacAddZImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 ×
        ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x1", enc a.1), ("y1", enc a.2.1), ("z1", enc a.2.2.1),
        ("x2", enc a.2.2.2.1), ("y2", enc a.2.2.2.2.1), ("z2", enc a.2.2.2.2.2.1)])
      (fun _ => True)
      (fun a => jacAddZLean a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1) := by
  ascend_reified jacAddZLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

/-- The typed literal of coordinate `i` of the addition over BabyBear. -/
def jacAddT : Fin 3 → TExpr
  | 0 => jacAddXT
  | 1 => jacAddYT
  | 2 => jacAddZT

/-- **The compiled bytes of the Jacobian addition over BabyBear.** For every coordinate `i`,
    if `compileA` returns `(P, bytes)` on `jacAddT i` under `addXAbi`, then from every entry
    state whose registers `%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `%r9` hold the canonical
    representatives of the six coordinates of `a`, the bytes decode to a program that halts in
    a state whose `%rax` reads back the encoding of coordinate `i` of the `add-2007-bl` sum
    `jacAddOps` of the two triples of `a`. -/
theorem jacAdd_bytes (i : Fin 3) (fname : String) {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA (jacAddT i) addXAbi fname = some (P, bytes)) (sa : AState)
    (a : ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 ×
      ZMod 2013265921 × ZMod 2013265921 × Unit)
    (h1 : a.1.val = (sa.regs "%rdi").toNat) (h2 : a.2.1.val = (sa.regs "%rsi").toNat)
    (h3 : a.2.2.1.val = (sa.regs "%rdx").toNat) (h4 : a.2.2.2.1.val = (sa.regs "%rcx").toNat)
    (h5 : a.2.2.2.2.1.val = (sa.regs "%r8").toNat)
    (h6 : a.2.2.2.2.2.1.val = (sa.regs "%r9").toNat) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ addXAbi.ResultOf sa sa'
        (enc (coord (jacAddOps (a.1, a.2.1, a.2.2.1) (a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1))
          i)) := by
  fin_cases i <;> simp only [jacAddT] at hc
  · have hf := jacAddX_fnCorres
    rw [← jacAddXT_erase] at hf
    exact addXAbi_bytes (by norm_num) jacAddXT fname hc jacAddX_spineLamFree _ hf sa a h1 h2 h3 h4 h5 h6
  · have hf := jacAddY_fnCorres
    rw [← jacAddYT_erase] at hf
    exact addXAbi_bytes (by norm_num) jacAddYT fname hc (by rw [jacAddYT_erase]; decide) _ hf sa a
      h1 h2 h3 h4 h5 h6
  · have hf := jacAddZ_fnCorres
    rw [← jacAddZT_erase] at hf
    exact addXAbi_bytes (by norm_num) jacAddZT fname hc (by rw [jacAddZT_erase]; decide) _ hf sa a
      h1 h2 h3 h4 h5 h6

/-! ## The doubling over BabyBear -/

/-- The `X` coordinate of the Jacobian double of `(x, y, z)` over BabyBear at the curve
    coefficient `a`. -/
def jacDblXLean (x y z a : ZMod 2013265921) : ZMod 2013265921 :=
  (jacDblOps a (x, y, z)).1

/-- The `Y` coordinate of the Jacobian double of `(x, y, z)` over BabyBear at the curve
    coefficient `a`. -/
def jacDblYLean (x y z a : ZMod 2013265921) : ZMod 2013265921 :=
  (jacDblOps a (x, y, z)).2.1

/-- The `Z` coordinate of the Jacobian double of `(x, y, z)` over BabyBear at the curve
    coefficient `a`. -/
def jacDblZLean (x y z a : ZMod 2013265921) : ZMod 2013265921 :=
  (jacDblOps a (x, y, z)).2.2

/-- The literal of `jacDblXLean`, with `jacDblOps` unfolded. -/
def jacDblXImp : ImpExpr := reifyField% jacDblXLean unfolding jacDblOps

/-- The literal of `jacDblYLean`, with `jacDblOps` unfolded. -/
def jacDblYImp : ImpExpr := reifyField% jacDblYLean unfolding jacDblOps

/-- The literal of `jacDblZLean`, with `jacDblOps` unfolded. -/
def jacDblZImp : ImpExpr := reifyField% jacDblZLean unfolding jacDblOps

theorem jacDblXImp_toTExpr_isSome : (jacDblXImp.toTExpr dblTypes).isSome = true := by
  rfl

theorem jacDblYImp_toTExpr_isSome : (jacDblYImp.toTExpr dblTypes).isSome = true := by
  rfl

theorem jacDblZImp_toTExpr_isSome : (jacDblZImp.toTExpr dblTypes).isSome = true := by
  rfl

/-- The typed literal of `jacDblXLean`, the four parameters typed as `u64` words. -/
def jacDblXT : TExpr := (jacDblXImp.toTExpr dblTypes).get jacDblXImp_toTExpr_isSome

/-- The typed literal of `jacDblYLean`, the four parameters typed as `u64` words. -/
def jacDblYT : TExpr := (jacDblYImp.toTExpr dblTypes).get jacDblYImp_toTExpr_isSome

/-- The typed literal of `jacDblZLean`, the four parameters typed as `u64` words. -/
def jacDblZT : TExpr := (jacDblZImp.toTExpr dblTypes).get jacDblZImp_toTExpr_isSome

theorem jacDblXT_erase : jacDblXT.erase = jacDblXImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacDblXImp_toTExpr_isSome).symm

theorem jacDblYT_erase : jacDblYT.erase = jacDblYImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacDblYImp_toTExpr_isSome).symm

theorem jacDblZT_erase : jacDblZT.erase = jacDblZImp :=
  ImpExpr.erase_toTExpr (Option.some_get jacDblZImp_toTExpr_isSome).symm

/-- From the entry environment binding `x`, `y`, `z`, `a`, the literal `jacDblXImp` returns
    the encoding of `jacDblXLean` under the table `hax64WExit`. -/
theorem jacDblX_fnCorres :
    FnCorres hax64WExit jacDblXImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1), ("z", enc a.2.2.1),
        ("a", enc a.2.2.2.1)])
      (fun _ => True) (fun a => jacDblXLean a.1 a.2.1 a.2.2.1 a.2.2.2.1) := by
  ascend_reified jacDblXLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

/-- From the entry environment binding `x`, `y`, `z`, `a`, the literal `jacDblYImp` returns
    the encoding of `jacDblYLean` under the table `hax64WExit`. -/
theorem jacDblY_fnCorres :
    FnCorres hax64WExit jacDblYImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1), ("z", enc a.2.2.1),
        ("a", enc a.2.2.2.1)])
      (fun _ => True) (fun a => jacDblYLean a.1 a.2.1 a.2.2.1 a.2.2.2.1) := by
  ascend_reified jacDblYLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

/-- From the entry environment binding `x`, `y`, `z`, `a`, the literal `jacDblZImp` returns
    the encoding of `jacDblZLean` under the table `hax64WExit`. -/
theorem jacDblZ_fnCorres :
    FnCorres hax64WExit jacDblZImp
      (A := ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × Unit)
      (fun a => bindParams [("x", enc a.1), ("y", enc a.2.1), ("z", enc a.2.2.1),
        ("a", enc a.2.2.2.1)])
      (fun _ => True) (fun a => jacDblZLean a.1 a.2.1 a.2.2.1 a.2.2.2.1) := by
  ascend_reified jacDblZLean using [hax64WExit_babyBear_mul, hax64WExit_babyBear_add,
    hax64WExit_babyBear_sub]

/-- The typed literal of coordinate `i` of the doubling over BabyBear. -/
def jacDblT : Fin 3 → TExpr
  | 0 => jacDblXT
  | 1 => jacDblYT
  | 2 => jacDblZT

/-- **The compiled bytes of the Jacobian doubling over BabyBear.** For every coordinate `i`,
    if `compileA` returns `(P, bytes)` on `jacDblT i` under `dblAbi`, then from every entry
    state whose registers `%rdi`, `%rsi`, `%rdx` hold the canonical representatives of the
    coordinates of a triple and `%rcx` that of the curve coefficient, the bytes decode to a
    program that halts in a state whose `%rax` reads back the encoding of coordinate `i` of
    the `dbl-2007-bl` double `jacDblOps` of the triple at that coefficient. -/
theorem jacDbl_bytes (i : Fin 3) (fname : String) {P : Lprog} {bytes : List (BitVec 8)}
    (hc : compileA (jacDblT i) dblAbi fname = some (P, bytes)) (sa : AState)
    (a : ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × ZMod 2013265921 × Unit)
    (h1 : a.1.val = (sa.regs "%rdi").toNat) (h2 : a.2.1.val = (sa.regs "%rsi").toNat)
    (h3 : a.2.2.1.val = (sa.regs "%rdx").toNat)
    (h4 : a.2.2.2.1.val = (sa.regs "%rcx").toNat) :
    ∃ prog sa', decodeLprog bytes = some prog ∧ Halts aMachine prog 0 sa sa'
      ∧ dblAbi.ResultOf sa sa'
        (enc (coord (jacDblOps a.2.2.2.1 (a.1, a.2.1, a.2.2.1)) i)) := by
  fin_cases i <;> simp only [jacDblT] at hc
  · have hf := jacDblX_fnCorres
    rw [← jacDblXT_erase] at hf
    exact dblAbi_bytes (by norm_num) jacDblXT fname hc (by rw [jacDblXT_erase]; decide) _ hf sa a
      h1 h2 h3 h4
  · have hf := jacDblY_fnCorres
    rw [← jacDblYT_erase] at hf
    exact dblAbi_bytes (by norm_num) jacDblYT fname hc (by rw [jacDblYT_erase]; decide) _ hf sa a
      h1 h2 h3 h4
  · have hf := jacDblZ_fnCorres
    rw [← jacDblZT_erase] at hf
    exact dblAbi_bytes (by norm_num) jacDblZT fname hc (by rw [jacDblZT_erase]; decide) _ hf sa a
      h1 h2 h3 h4

end CatCrypt.Crypto.SecureCompilation.Haxc
