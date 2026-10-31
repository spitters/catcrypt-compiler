/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.ComposeV1
public import CatCrypt.Crypto.SecureCompilation.Haxc.AndnLegalComplete
public meta import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin
public import CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFn
public meta import CatCrypt.Crypto.Jasmin.JazzRoundTrip
public import CatCrypt.Crypto.Jasmin.JazzRoundTrip

@[expose] public section

set_option autoImplicit false

/-!
# Jasmin source of the program `compileA` compiles

`jasminOfA` prints, as Jasmin source, the structured program that `compileA` compiles to
machine code; it is produced on request beside the owned machine code, which is the default
artifact. It reads the structured program at the named stage `NFEntry.chainNF` of
`compileA` (after the pair stage `pairStage`, the translation of the hax entry `haxEntry` and
the chain `extChain`), the same stage `NFEntry.compileR` passes to the region back half
`compileRegion`, and applies its exportability test `regionExportableB`. On that program the lowering
`nfToJasmin` builds a Jasmin compilation unit under the signature `jazzSigOf` of the layout,
and the single Jasmin printer prints it through the gate `Jazz.printChecked`, which returns
the text only when it parses back to the erasure of the unit.

The signature `jazzSigOf σ t` declares the parameters of `σ` in argument order: a scalar
parameter in a register, an input array as a `reg ptr`, the array that holds the result as a
`reg mut ptr`. A scalar result (`.reg`) is
returned in a register; an array result (`.words r n`) is the `reg mut ptr` parameter whose
register is `r`. A layout with another result has no signature.

## Main results

* `jazzSigOf` — the Jasmin signature of a layout at a result type.
* `NFEntry.jasminOfChain`, `NFEntry.jasminOfChain_spec` — the Jasmin source of the
  structured program of the compiler at an entry: a text it returns parses to the unit
  `nfToJasmin` builds from the program of the stage `chainNF`, without the extern signatures
  of the unit.
* `jasminOfA`, `jasminOfA_same_program` — the Jasmin source at the hax entry
  after the pair stage; when `compileA` also returns a result, both results come from the
  same structured program: the one `compileRegion` compiles to that result is the one
  `nfToJasmin` lowers to the unit the text parses to.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions (regionExportableB)
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasmin (JazzSig nfToJasmin ptyOf nfToJasmin_erase)
open CatCrypt.Crypto.Jasmin.Jazz (Storage JazzUnit)
open CatCrypt.Crypto.Jasmin.JazzToInstrR (parseUnit)
open CatCrypt.Crypto.Hax (HaxModule)

/-! ## 1. The signature of a layout -/

/-- The storage class of an input parameter of a dialect type: a read-only `reg ptr` for an
    array, a register otherwise. The array that holds the result is a `reg mut ptr`
    (`jazzSigOf`); jasminc refuses a mutable pointer that a function does not return. -/
def jazzStorOf : JasminTy → Storage
  | .stackArr _ _ => .regPtr false
  | _ => .reg

/-- The index of the parameter that holds the result of the layout `σ`, when the result is an
    array. -/
def jazzResIdx (σ : AbiLayout) : Option Nat :=
  match σ.result with
  | .words r _ => σ.args.findIdx? (·.reg == r)
  | _ => none

/-- **The Jasmin signature of a layout** at the result type `t`: the parameters of the
    context `nfCtx σ` in argument order, each named by its parameter of `σ`, with the storage
    class `jazzStorOf` (a `reg mut ptr` for the parameter `jazzResIdx σ` that holds the
    result) and the surface type `ptyOf` of its type; a scalar result in a
    register; an array result `.words r n` held by the parameter whose register is `r`.
    `none` at another result, or when no parameter has the register of the result. -/
def jazzSigOf (σ : AbiLayout) (t : JasminTy) : Option (JazzSig (nfCtx σ) t) :=
  let ps := (nfCtx σ).reverse.mapIdx fun j ty =>
    (((σ.args[j]?).map (·.name)).getD "",
      (if jazzResIdx σ = some j then .regPtr true else jazzStorOf ty), ptyOf ty)
  have hps : ps.length = (nfCtx σ).length := by simp [ps]
  match σ.result with
  | .reg _ => some ⟨ps, (.reg, ptyOf t), none, hps⟩
  | .words r _ =>
      (σ.args.findIdx? (·.reg == r)).map fun j => ⟨ps, (.regPtr true, ptyOf t), some j, hps⟩
  | _ => none

/-! ## 2. The Jasmin source of the structured program at an entry -/

/-- **The Jasmin source of the structured program of the compiler at an entry**: the stage
    `NFEntry.chainNF` (the translation and the chain of `NFEntry.compileR`), the test
    `regionExportableB` of `compileRegion`, the lowering `nfToJasmin` under the signature
    `jazzSigOf σ`, and the printer gate `Jazz.printChecked`. -/
def NFEntry.jasminOfChain (E : NFEntry) (s : E.Src) (σ : AbiLayout) (fname : String) :
    Option String :=
  (E.chainNF s σ).bind fun x =>
    if regionExportableB x.2 = true then
      (jazzSigOf σ x.1).bind fun sig =>
        (nfToJasmin sig fname x.2).bind CatCrypt.Crypto.Jasmin.Jazz.printChecked
    else none

/-- **A text of `NFEntry.jasminOfChain` is the source of the program of the chain.** The
    stage `chainNF` returns the program `x.2`, it passes `regionExportableB`, the layout has
    a signature `sig`, `nfToJasmin` returns the unit `u` on it, and the text parses to `u`
    without its extern signatures. -/
theorem NFEntry.jasminOfChain_spec {E : NFEntry} {s : E.Src} {σ : AbiLayout}
    {fname str : String} (h : E.jasminOfChain s σ fname = some str) :
    ∃ (x : Σ t : JasminTy, NFProg jasminDialect (nfCtx σ) [t])
      (sig : JazzSig (nfCtx σ) x.1) (u : JazzUnit),
      E.chainNF s σ = some x ∧ regionExportableB x.2 = true ∧ jazzSigOf σ x.1 = some sig ∧
        nfToJasmin sig fname x.2 = some u ∧ parseUnit str = .ok { u with externs := [] } := by
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i he
    obtain ⟨sig, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u, hu, h⟩ := Option.bind_eq_some_iff.mp h
    refine ⟨x, sig, u, hx, he, hs, hu, ?_⟩
    rw [(CatCrypt.Crypto.Jasmin.Jazz.printChecked_sound h).2, nfToJasmin_erase hu]
  · cases h

/-! ## 3. The Jasmin source of the hax compiler -/

/-- **The Jasmin source of the program `compileA` compiles**: the pair stage `pairStage`,
    then `NFEntry.jasminOfChain` at the hax entry `haxEntry`, as `compileA` runs
    `compileARegion` after the pair stage. -/
def jasminOfA (m : HaxModule) (σ : AbiLayout) (fname : String) : Option String :=
  haxEntry.jasminOfChain (pairStage m σ).1 (pairStage m σ).2 fname

/-- **Both back ends compile the same structured program.** Let `jasminOfA` return the text
    `str` and `compileA` return `(P, bytes)` on the same module, layout and symbol. Then the
    stage `chainNF` returns one structured program `x.2` such that `compileRegion` returns
    `(P, bytes)` on it at the linked functions of the module, and `nfToJasmin` returns on it a
    unit `u` to which `str` parses, without the extern signatures of `u`. -/
theorem jasminOfA_same_program {m : HaxModule} {σ : AbiLayout}
    {fname str : String} {P : Lprog} {bytes : List (BitVec 8)}
    (hJ : jasminOfA m σ fname = some str) (hA : compileA m σ fname = some (P, bytes)) :
    ∃ (x : Σ t : JasminTy, NFProg jasminDialect (nfCtx (pairStage m σ).2) [t])
      (sig : JazzSig (nfCtx (pairStage m σ).2) x.1) (u : JazzUnit),
      compileRegion (pairStage m σ).2 (haxEntry.names fname (pairStage m σ).2) x.2
          ((pairStage m σ).1.linked.filterMap CatCrypt.Crypto.Hax.LinkedFn.calleeData) =
        some (P, bytes) ∧
        nfToJasmin sig fname x.2 = some u ∧ parseUnit str = .ok { u with externs := [] } := by
  obtain ⟨x, sig, u, hx, -, -, hu, hs⟩ := NFEntry.jasminOfChain_spec hJ
  obtain ⟨x', hx', hA⟩ := Option.bind_eq_some_iff.mp hA
  rw [hx] at hx'
  cases hx'
  exact ⟨x, sig, u, hA, hu, hs⟩

/-! ## 4. The Jasmin source in the mirror semantics -/

section Mirror
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSem (JazzValAgrees JazzOpAgrees IdxInBounds)
open CatCrypt.Crypto.SecureCompilation.VIR.NFToJasminSemFn (JazzCallsAgree JazzArgsAgree
  nfToJasmin_sem)
open CatCrypt.Crypto.SecureCompilation.VIR.InstrRTranslateJazz (translateUnit)
open CatCrypt.Crypto.SecureCompilation.VIR.JazzAsmSem (JazzAsmAgrees)
open CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry (AbiValOf)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.Jasmin.CoqSemMirror (AsmSem OpSem GlobDecls Prog SemCall MemModel
  getFunDef)

variable {SyscallState Mem : Type} [MemModel Mem]

/-- The mirror arguments `vargs`, in parameter order, hold every valuation that the layout
    `σ` reads off the entry state `sa`. -/
def ArgsOfState (σ : AbiLayout) (sa : AState)
    (vargs : List CatCrypt.Crypto.Jasmin.CoqSemMirror.Value) : Prop :=
  ∀ V : Ctxt.Valuation (nfCtx σ), AbiValOf σ sa V → JazzArgsAgree V vargs

/-- The mirror results `vres` are one value that holds a dialect value whose source value is
    `v`: a word for a scalar result, a byte array whose little-endian words are the elements
    for an array result. -/
def ResultOfJazz (vres : List CatCrypt.Crypto.Jasmin.CoqSemMirror.Value) (v : _root_.Hax.Value) :
    Prop :=
  ∃ (t : JasminTy) (x : ⟦t⟧) (w : CatCrypt.Crypto.Jasmin.CoqSemMirror.Value),
    vres = [w] ∧ JazzValAgrees t x w ∧ v = denVal t x

/-- **The Jasmin source of the compiler at an entry runs in the mirror.** Let
    `NFEntry.jasminOfChain` return the text `str` (at a layout whose result is a register or
    an array returned through its `reg mut ptr` parameter), let `str` parse to a unit that translates to the mirror program `prog`, and let `P` be a
    mirror program that defines `fname` as `prog` does and whose callees agree with the call
    environment of the entry at every fuel. Let the structured program of the stage
    `chainNF` call only declared procedures, and let its
    array indices be in range at the valuations the layout reads off the entry state `sa`.
    Then for every value `v` of a source run from `sa`, the function `fname` of `P` runs,
    from every syscall state and memory and from arguments that hold the valuation of `sa`,
    to the same syscall state and memory and to one result that holds a value whose source
    value is `v`. -/
theorem NFEntry.jasminOfChain_sem {E : NFEntry} {s : E.Src} {σ : AbiLayout}
    {fname str : String} (h : E.jasminOfChain s σ fname = some str)
    (hchain : ∀ x, E.chainNF s σ = some x →
      onlyCalls (declSigs (E.decls s)) x.2 = true)
    {u : JazzUnit} (hu : parseUnit str = .ok u) {prog : Prog}
    (hprog : translateUnit u = some prog) {aS : AsmSem} (haS : JazzAsmAgrees aS) {opS : OpSem}
    (hop : JazzOpAgrees opS) {gd : GlobDecls} {P : Prog}
    (hP : getFunDef P ⟨fname⟩ = getFunDef prog ⟨fname⟩)
    (hE : ∀ fuel, JazzCallsAgree SyscallState Mem aS opS gd P (E.env s fuel))
    (sa : AState) (hsep : σ.Regions sa) (v : _root_.Hax.Value) (hrun : E.Runs σ s sa v)
    (hidx : ∀ x fuel (V : Ctxt.Valuation (nfCtx σ)), E.chainNF s σ = some x →
      AbiValOf σ sa V → IdxInBounds (E.env s fuel) fuel x.2 V)
    (scs : SyscallState) (m : Mem) {vargs : List CatCrypt.Crypto.Jasmin.CoqSemMirror.Value}
    (hargs : ArgsOfState σ sa vargs) :
    ∃ vres, SemCall aS opS gd P scs m ⟨fname⟩ vargs scs m vres ∧ ResultOfJazz vres v := by
  obtain ⟨x, sig, u0, hx, hex, -, hu0, hparse⟩ := NFEntry.jasminOfChain_spec h
  rw [hu] at hparse
  cases hparse
  have hprog' : translateUnit u0 = some prog := hprog
  have honly := hchain x hx
  have hexL : regionExportableB (legalizeRegion x.2) = true := by
    unfold legalizeRegion
    rw [legalizeRor_eq_of_regionExportableB hex]
    exact regionExportableB_legalizeAndn hex
  have hf : E.frontR σ s = some ⟨nfCtx σ, x.1, .regions x.2⟩ := by
    unfold NFEntry.chainNF at hx
    obtain ⟨q, hq, hx⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hx
    unfold NFEntry.frontR
    rw [hq, Option.bind_some, hp', Option.bind_some]
    simp [exportRegion, hexL, honly]
  obtain ⟨V, fuel, y, hV, hy, hv⟩ := E.toFrontLegOfR.leg σ s _ hf sa v hsep hrun
  change (x.2.denoteAt (E.env s fuel) fuel V).map oneResult = some y at hy
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp hy
  obtain ⟨z, rfl⟩ : ∃ z, w = .cons z .nil := by
    cases w with
    | cons z r1 => cases r1; exact ⟨z, rfl⟩
  obtain ⟨wv, hsem, hagr⟩ := nfToJasmin_sem aS opS gd haS hop hu0 hprog' hP (hE fuel)
    hw (hidx x fuel V hx hV) scs m (hargs V hV)
  exact ⟨[wv], hsem, x.1, z, wv, rfl, hagr, hv⟩

end Mirror

end CatCrypt.Crypto.SecureCompilation.Haxc
