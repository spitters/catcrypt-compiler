/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
public import CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttWord
public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteChain
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

@[expose] public section

set_option autoImplicit false

/-!
# The NTT route: a lane program to a route's program over word arrays

A lane program `m : MultiReturnCom jasminDialect (Rn N) (Rn N)` maps `N` word registers to
`N` word registers. `lanesCom m` is the straight-line program over an input array and an
output array of `N` words that loads the `N` input words, runs `m` on them and stores its
`N` results into the output array, returning the last stored array. The forward and inverse
word transforms `nttProgW` and `inttProgW` of `VIR/NegacyclicNttWord.lean`, for every
parameter record `P : NttParams` and lazy schedule `S`, give the route programs
`nttRoute P S logR` and `inttRoute P S logR s` on `2 ^ P.logN` words.

The lane route is the run of a `PassChain.Chain` of the shape `lanesChainVia opt`: the
optimisation step `opt` on `MultiReturnCom jasminDialect`, the lane lowering `lanesCom`
(`lanesStep`) and the route wrapper. `nttRoute` and `inttRoute` are runs of `lanesChainId`,
the lane chain at the identity step `Step.id`; `FieldChain.lanesChain` is the same shape at
the value numbering `gvnMR`.

The System V layout `lanesAbi N` passes the output array in `%rdi` and the input array in
`%rsi`, each a `words N` parameter, and reads back the `N` words at the entry `%rdi`;
`abiValL N sa` is the valuation of the program's context read off a machine state `sa`, and
`abiValOf_lanesAbi` states that the layout reads it off `sa` (`AbiValOf`).

## Main results

* `lanesCom`, `lanesCom_denote`, `stackGet_lanesCom`: the program over word arrays of a
  lane program, its output array, and word `i` of the output array as lane `i` of the lane
  program at the input words.
* `mrSem`, `lanesStep`, `lanesCert`: the semantics of multi-return programs, and the lane
  lowering as a chain step with its certificate.
* `lanesChainVia`, `lanesChainViaCert`, `lanesChainVia_denote`, `lanesChainId`: the lane
  chain at an optimisation step, its certificate, the output words of a program it
  produces, and the lane chain at the identity step.
* `lanesAbi`, `abiValL`, `abiValOf_lanesAbi`: the layout and the valuation it reads off a
  machine state.
* `nttRoute`, `nttRoute_denote`: the route program of the forward transform, and its
  output words, below `bnd P S P.layers` and congruent to `nttSpec` of the input words.
* `inttRoute`, `inttRoute_denote`: the route program of the inverse transform, and its
  output words, below `2 q` and congruent to `inttSpec` of the input words.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.FieldDialectBlockDescent (pullV)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Curve25519 (MC)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-! ## 1. A lane program over word arrays -/

section Lanes

variable {N : Nat}

/-- The context of a lane program over word arrays: the input array, then the output
    array, each of `N` words. -/
abbrev lanesCtx (N : Nat) : Ctxt jasminDialect := [arrTy N, arrTy N]

/-- **A lane program over word arrays, as a multi-result program**: the loads of the `N`
    words of the input array, the lane program `m` on the loaded words, and the stores of
    its `N` results into the output array; the program returns the last stored array. -/
def lanesBody (m : MultiReturnCom jasminDialect (Rn N) (Rn N)) :
    MC (lanesCtx N) [arrTy N] :=
  loadLimbs N 0 .here fun r h =>
    spliceMultiK (MultiReturnCom.rename h m) fun r₂ res =>
      storeLimbs N 0 (r₂ (r (.there .here))) (hvToHom res)

/-- **A lane program over word arrays.** -/
def lanesCom (m : MultiReturnCom jasminDialect (Rn N) (Rn N)) :
    Com jasminDialect (lanesCtx N) (arrTy N) :=
  (lanesBody m).toComHead

theorem lanesBody_denote (hN : N < 2 ^ 64) (m : MultiReturnCom jasminDialect (Rn N) (Rn N))
    (a o : Fin N → BitVec 64) :
    (lanesBody m).denote (.cons a (.cons o .nil))
      = .cons (storeVal o 0 (m.denote (arrLimbs a N 0))) .nil := by
  refine loadLimbs_denote N 0 _ _ _ _ (by omega) fun r h W' hr hh => ?_
  refine spliceMultiK_denote _ _ W' _ fun r₂ res W'' h₂ hres => ?_
  rw [storeLimbs_denote hN N 0 _ _ W'' (by omega), h₂, hr, pullV_hvToHom, hres,
    multiReturnCom_denote_rename, hh]
  rfl

/-- **The output array of a lane program over word arrays**: the output array `o` with the
    results of the lane program at the input words written from index `0`. -/
theorem lanesCom_denote (hN : N < 2 ^ 64) (m : MultiReturnCom jasminDialect (Rn N) (Rn N))
    (a o : Fin N → BitVec 64) :
    (lanesCom m).denote (.cons a (.cons o .nil)) = storeVal o 0 (m.denote (arrLimbs a N 0)) := by
  rw [lanesCom, MultiReturnCom.toComHead_denote, lanesBody_denote hN m a o]
  rfl

/-- The words of an array from index `j` are the lanes of its word function from `j`. -/
theorem arrLimbs_eq_lanesVal (a : Fin N → BitVec 64) :
    ∀ (k j : Nat), arrLimbs a k j = lanesVal R64 (fun i => stackGet a i) k j
  | 0, _ => rfl
  | k + 1, j => by
      show HVector.cons _ (arrLimbs a k (j + 1)) = HVector.cons _ _
      rw [arrLimbs_eq_lanesVal a k (j + 1)]

/-- **Word `i` of the output array of a lane program** is lane `i` of the lane program at
    the input words. -/
theorem stackGet_lanesCom (hN : N < 2 ^ 64) (m : MultiReturnCom jasminDialect (Rn N) (Rn N))
    (a o : Fin N → BitVec 64) (i : Nat) (hi : i < N) :
    stackGet ((lanesCom m).denote (.cons a (.cons o .nil))) i
      = hvGetG R64 (0 : BitVec 64) (m.denote (lanesVal R64 (fun j => stackGet a j) N 0)) i := by
  rw [lanesCom_denote hN m a o, ← arrLimbs_eq_lanesVal]
  have e := arrLimbs_storeVal o 0 (m.denote (arrLimbs a N 0)) (by omega)
  rw [arrLimbs_eq_lanesVal] at e
  conv_rhs => rw [← e]
  rw [hvGetG_lanesVal _ _ _ _ _ _ hi, Nat.zero_add]

end Lanes

end CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute

/-! ## 2. The lane chain -/

namespace CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.VIR.PassChain
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.Haxc (RouteProg)
open CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute (lanesCtx lanesCom lanesCom_denote)

/-- The semantics of multi-return programs of `d` over `Γ` returning `ts`: every run
    succeeds with the denotation. -/
def mrSem (d : Dialect.{0, 0}) [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
    (Γ : Ctxt d) (ts : List d.Ty) : Sem (MultiReturnCom d Γ ts) where
  In := Valuation Γ
  Out := Valuation ts
  den m V := some (m.denote V)

variable {N : Nat}

/-- The lane lowering `lanesCom` of a lane program over `N` words as a chain step. -/
def lanesStep (N : Nat) :
    Step (MultiReturnCom jasminDialect (Rn N) (Rn N)) (Com jasminDialect (lanesCtx N) (arrTy N)) :=
  ⟨"lanes", fun m => some (lanesCom m)⟩

/-- The certificate of the lane lowering: the input relation says the input array holds
    the input words and the output array is arbitrary, and the output relation reads the
    words of the output array. -/
def lanesCert (hN : N < 2 ^ 64) :
    StepCert (lanesStep N).run (mrSem jasminDialect (Rn N) (Rn N))
      (comSemOf jasminDialect (lanesCtx N) (arrTy N)) where
  relIn V W := ∃ a o : Fin N → BitVec 64,
    @Eq (Valuation (lanesCtx N)) W (.cons a (.cons o .nil)) ∧ V = arrLimbs a N 0
  relOut x y := arrLimbs y N 0 = x
  sound := by
    intro m q V W x hf hVW hd
    obtain ⟨a, o, rfl, rfl⟩ := hVW
    cases hf
    cases hd
    refine ⟨_, rfl, ?_⟩
    show arrLimbs ((lanesCom m).denote (.cons a (.cons o .nil))) N 0 = _
    rw [lanesCom_denote hN m a o]
    exact arrLimbs_storeVal o 0 _ (by omega)

/-- **The lane chain at the optimisation step `opt`**: the step `opt` on lane programs, the
    lane lowering and the route wrapper. -/
def lanesChainVia
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N))) :
    Chain (MultiReturnCom jasminDialect (Rn N) (Rn N)) (RouteProg (lanesCtx N) (arrTy N)) :=
  .cons opt <| .cons (lanesStep N) <| .cons (straightStep _ _) <| .nil _

/-- **The certificate of the lane chain at `opt`**, for a step `opt` whose output has the
    denotation of its input (`hopt`). -/
def lanesChainViaCert (hN : N < 2 ^ 64)
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N)))
    (hopt : ∀ m q, opt.run m = some q → q.denote = m.denote) :
    Cert (lanesChainVia opt) (mrSem jasminDialect (Rn N) (Rn N))
      (routeSem (lanesCtx N) (arrTy N)) :=
  .cons (StepCert.ofDenoteEq _ fun m q hf => by
      funext V
      show some _ = some _
      rw [hopt m q hf]) <|
    .cons (lanesCert hN) <| .cons (straightCert _ _) <| .nil _

/-- **The output words of a program of the lane chain at `opt`**, from `Cert.sound`: the
    words of the output array are the results of the lane program at the input words. -/
theorem lanesChainVia_denote (hN : N < 2 ^ 64)
    (opt : Step (MultiReturnCom jasminDialect (Rn N) (Rn N))
      (MultiReturnCom jasminDialect (Rn N) (Rn N)))
    (hopt : ∀ m q, opt.run m = some q → q.denote = m.denote)
    {m : MultiReturnCom jasminDialect (Rn N) (Rn N)} {rp : RouteProg (lanesCtx N) (arrTy N)}
    (hrun : (lanesChainVia opt).run m = some rp) (a o : Fin N → BitVec 64) :
    arrLimbs (rp.denote (.cons a (.cons o .nil))) N 0 = m.denote (arrLimbs a N 0) := by
  obtain ⟨o', ho', x, hx, y, hy, z, hz, hzo⟩ :=
    (lanesChainViaCert hN opt hopt).sound (V := arrLimbs a N 0) (W := .cons a (.cons o .nil))
      (o := m.denote (arrLimbs a N 0)) hrun
      ⟨_, rfl, _, ⟨a, o, rfl, rfl⟩, _, rfl, rfl⟩ rfl
  cases ho'
  cases hx
  cases hz
  cases hzo
  exact hy

/-- **The lane chain at the identity step.** -/
def lanesChainId (N : Nat) :
    Chain (MultiReturnCom jasminDialect (Rn N) (Rn N)) (RouteProg (lanesCtx N) (arrTy N)) :=
  lanesChainVia (Step.id _)

/-- The lane chain at the identity step runs to the lane lowering of its input. -/
theorem lanesChainId_run (m : MultiReturnCom jasminDialect (Rn N) (Rn N)) :
    (lanesChainId N).run m = some (.straight (lanesCom m)) :=
  rfl

end CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.Ctxt
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.MultiBlockLowering
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldLimbs.Mont (Rn)
open CatCrypt.Crypto.SecureCompilation.Algebraic.FieldToJasminLimbs
open CatCrypt.Crypto.SecureCompilation.VIR.NegacyclicNttTemplate
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf wordsFn)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc.FieldChain (lanesChainId lanesChainId_run)

/-! ## 3. The layout of a lane program over word arrays -/

/-- **The layout of a lane program over `N` words**: the output array in `%rdi`, the input
    array in `%rsi`, each of `N` words; the result is the `N` words at the entry `%rdi`; the
    body's stack words lie in the `4096` bytes below the entry `%rsp`. -/
def lanesAbi (N : Nat) : AbiLayout where
  args := [⟨"out", "%rdi", .words N⟩, ⟨"a", "%rsi", .words N⟩]
  consts := []
  result := .words "%rdi" N
  bounds := []
  frameLo := -4096
  frameHi := -8

/-- The valuation of the context of a lane program over word arrays read off the machine
    state `sa`: the `N` words at the entry `%rsi` and `%rdi`. -/
def abiValL (N : Nat) (sa : AState) : Valuation (lanesCtx N) :=
  .cons (wordsFn sa (sa.regs "%rsi") N) (.cons (wordsFn sa (sa.regs "%rdi") N) .nil)

theorem abiValOf_lanesAbi (N : Nat) (sa : AState) :
    AbiValOf (lanesAbi N) sa (abiValL N sa) where
  arg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩ <;> rfl
  reg := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩
  arr := fun v => by
    rcases v with _ | _ | ⟨⟨⟩⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## 4. The forward and inverse transforms -/

section Ntt

variable (P : NttParams) (S : LazySched) (logR : Nat)

/-- **The route program of the forward transform** on `2 ^ P.logN` words: the run of the
    lane chain at the identity step on `nttProgW P S logR`. -/
def nttRoute : RouteProg (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN)) :=
  ((lanesChainId (2 ^ P.logN)).run (nttProgW P S logR)).get rfl

/-- **The route program of the inverse transform** of scaling constant `s` on
    `2 ^ P.logN` words: the run of the lane chain at the identity step on
    `inttProgW P S logR s`. -/
def inttRoute (s : Nat) : RouteProg (lanesCtx (2 ^ P.logN)) (arrTy (2 ^ P.logN)) :=
  ((lanesChainId (2 ^ P.logN)).run (inttProgW P S logR s)).get rfl

/-- The lane chain at the identity step runs on the forward transform to `nttRoute`. -/
theorem lanesChainId_run_ntt :
    (lanesChainId (2 ^ P.logN)).run (nttProgW P S logR) = some (nttRoute P S logR) :=
  (Option.some_get _).symm

/-- The lane chain at the identity step runs on the inverse transform to `inttRoute`. -/
theorem lanesChainId_run_intt (s : Nat) :
    (lanesChainId (2 ^ P.logN)).run (inttProgW P S logR s) = some (inttRoute P S logR s) :=
  (Option.some_get _).symm

/-- **The output words of the forward transform route.** For a parameter record satisfying
    `NttParams.Ok`, a schedule satisfying `SchedOk` and `WordOk`, and input words below
    `q`, every output word is below `bnd P S P.layers`, and cast to `ZMod q` it is
    `nttSpec` of the input words. -/
theorem nttRoute_denote (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (hS : SchedOk P S)
    (hW : WordOk P S logR) (a o : Fin (2 ^ P.logN) → BitVec 64)
    (ha : ∀ j, (stackGet a j).toNat < P.q) (i : Nat) (hi : i < 2 ^ P.logN) :
    (stackGet ((nttRoute P S logR).denote (.cons a (.cons o .nil))) i).toNat
        < bnd P S P.layers ∧
    (((stackGet ((nttRoute P S logR).denote (.cons a (.cons o .nil))) i).toNat : Nat)
        : ZMod P.q)
      = nttSpec (P.psi : ZMod P.q) P.layers P.logN
          (fun j => ((stackGet a j).toNat : ZMod P.q)) i := by
  have e : (fun j => stackGet a j) = fun j => BitVec.ofNat 64 (stackGet a j).toNat :=
    funext fun j => by simp
  rw [Option.some_inj.mp ((lanesChainId_run _).symm.trans (lanesChainId_run_ntt P S logR)).symm,
    RouteProg.denote_straight, stackGet_lanesCom hN _ a o i hi, e]
  exact nttProgW_denote P S logR hP hS hW _ ha i hi

/-- **The output words of the inverse transform route.** For a parameter record satisfying
    `NttParams.Ok`, a schedule satisfying `SchedOk`, `WordOk` and `InvWordOk`, and input
    words at most `R`, every output word is below `2 q`, and cast to `ZMod q` it is
    `inttSpec` of the input words. -/
theorem inttRoute_denote (hN : 2 ^ P.logN < 2 ^ 64) (hP : P.Ok) (hS : SchedOk P S)
    (hW : WordOk P S logR) (hI : InvWordOk P S) (s : Nat) (a o : Fin (2 ^ P.logN) → BitVec 64)
    (ha : ∀ j, (stackGet a j).toNat ≤ S.R) (i : Nat) (hi : i < 2 ^ P.logN) :
    (stackGet ((inttRoute P S logR s).denote (.cons a (.cons o .nil))) i).toNat < 2 * P.q ∧
    (((stackGet ((inttRoute P S logR s).denote (.cons a (.cons o .nil))) i).toNat : Nat)
        : ZMod P.q)
      = inttSpec (P.psi : ZMod P.q) P.layers P.logN (s : ZMod P.q)
          (fun j => ((stackGet a j).toNat : ZMod P.q)) i := by
  rw [Option.some_inj.mp
      ((lanesChainId_run _).symm.trans (lanesChainId_run_intt P S logR s)).symm,
    RouteProg.denote_straight, stackGet_lanesCom hN _ a o i hi]
  exact inttProgW_denote_words P S logR hP hS hW hI s _ ha i hi

end Ntt

end CatCrypt.Crypto.SecureCompilation.Haxc.NttRoute
