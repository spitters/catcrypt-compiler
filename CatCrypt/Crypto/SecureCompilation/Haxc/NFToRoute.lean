/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Hax.NFToCat
public import CatCrypt.Crypto.SecureCompilation.Haxc.RouteProg
public import CatCrypt.Crypto.SecureCompilation.X86Backend.ExportCertEntry

/-!
# The result types and the entry of a route program of `NFProg nfDialect`

A program of `NFProg nfDialect` with one result is lowered by the chain to a program of
`jasminDialect` (a `RouteProgJ`, whose structured programs the region back half
`RegionBackend.compileRegion` takes). The context of the lowered program is
`mapCtx (Γ.map catTy)`, its valuation the mapped valuation `ctMapValD (mapVal V)`. This module
holds the result types the back half reads back and the reading of the entry parameters off
an entry state.

## Main definitions

* `OutTy` — the result types the back half reads back: words, integers and arrays of words.
* `abiEntry`, `SlotOK` — the parameters of a layout as the entry of a program, last
  parameter newest, and the reading of a parameter off an entry state at a jasmin type.

## Main results

* `denVal_ctTransTy` — at a result type, the source value of a target value related to a
  source value is the encoding of the source value.
* `abiValOf_mapVal`, `inRange_entry` — the mapped valuation of the entry parameters is the
  valuation the layout reads off the entry state, and the entry valuation is in range.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.DialectToJasminComCorrect (ctMapValD)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy mapCtx)
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminComCorrect (ctTransTy)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (enc PDenP entryCtx EntryVals)
open Ctxt (Var Valuation)
open _root_.Hax (Value)

/-- The result types the back half reads back: words, integers and arrays of words. -/
def OutTy : NfTy → Prop
  | .word _ => True
  | .int => True
  | .arr _ (.word _) => True
  | _ => False

/-- **The read-back of a result.** At a result type, the source value `denVal` of the
    transported target value related to a source value is the encoding of the source
    value. -/
theorem denVal_ctTransTy : ∀ (t : NfTy), OutTy t → ∀ (y : t.denote) (x : (catTy t).denote),
    VRel t y x → denVal (mapTy (catTy t)) (ctTransTy x) = enc t y
  | .word _, _, y, x, h => by
      change Value.int x.toNat = Value.int y.toNat
      rw [show y = x from h]
  | .int, _, y, x, h => by
      change Value.int x.toNat = Value.int y
      rw [show y = (x.toNat : Int) from h]
  | .arr n (.word _), _, f, g, h => by
      change Value.array ((List.range n).map fun j => .int (stackGet g j).toNat) =
        Value.array (List.ofFn fun i => Value.int ((f i).toNat : Nat))
      congr 1
      apply List.ext_getElem (by simp)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      rw [show (f ⟨j, by simpa using h2⟩).toNat = _ from h ⟨j, by simpa using h2⟩]
      congr 3
      cases n with
      | zero => simp at h1
      | succ m =>
          simp only [stackGet]
          congr 1
          exact Fin.ext (Nat.mod_eq_of_lt (by simpa using h1))

/-! ## The reading of the entry -/

/-- The parameters of a System V layout as the entry of a program: the last parameter is
    the newest variable, so that the variable at de Bruijn index `k` of the mapped context
    reads the parameter at slot `argIdx`. -/
def abiEntry (σ : AbiLayout) : List (String × NfTy) := (abiParamsArr σ).reverse

/-- A value of the jasmin type `t` is the reading of the parameter `a` off the entry state
    `sa`: a `64`-bit register the register of a scalar parameter, an array of `n` `64`-bit
    words the words at the address of an array parameter of `n` words. -/
def SlotOK (sa : Ascent.AddrMem.AState) (a : AbiArg) : (t : JasminTy) → ⟦t⟧ → Prop
  | .reg w, x => a.kind = .scalar ∧ ∃ h : w = 64, x = h ▸ sa.regs a.reg
  | .stackArr w n, x => a.kind = .words n ∧
      ∃ h : w = 64, x = h ▸ X86Backend.ExportCertEntry.wordsFn sa (sa.regs a.reg) n
  | _, _ => False

/-- Every variable of the mapped context of the parameters `as` reads, in the mapped
    valuation of a valuation whose encodings the environment holds, the parameter at its de
    Bruijn index. -/
theorem slotOK_lookup (sa : Ascent.AddrMem.AState) {env : _root_.Hax.Env} :
    ∀ (as : List AbiArg), (∀ a ∈ as, env a.name = some (a.read sa)) →
      ∀ (V : Valuation (entryCtx (as.map fun a => (a.name, abiKindArr a.kind)))),
      EntryVals env (as.map fun a => (a.name, abiKindArr a.kind)) V →
      ∀ {t : JasminTy} (v : Var (d := jasminDialect)
        (mapCtx ((entryCtx (as.map fun a => (a.name, abiKindArr a.kind))).map catTy))
        t),
      ∃ a, as[JasminLprogExport.varIndex v]? = some a ∧
        SlotOK sa a t (v.lookup (ctMapValD (mapVal V)))
  | [], _, .nil, _, _, v => nomatch v
  | a :: as, h, .cons y V, ⟨hy, hV⟩, t, v => by
      cases v with
      | here =>
          refine ⟨a, rfl, ?_⟩
          have hr := h a List.mem_cons_self
          obtain ⟨name, reg, kind⟩ := a
          cases kind with
          | scalar =>
              have hy' : enc (abiKindArr .scalar) y = enc (abiKindArr .scalar) (sa.regs reg) :=
                Option.some.inj (hy.symm.trans hr)
              obtain rfl := enc_inj_abi hy'
              exact ⟨rfl, rfl, rfl⟩
          | words n =>
              have hy' : enc (abiKindArr (.words n)) y = enc (abiKindArr (.words n))
                  (fun k => Ascent.AddrMem.read64 sa.mem
                    (sa.regs reg + BitVec.ofNat 64 (8 * k.1))) := by
                refine (Option.some.inj (hy.symm.trans hr)).trans ?_
                simp only [AbiArg.read, wordsAt, abiKindArr, enc]
                congr 1
                apply List.ext_getElem <;> simp
              obtain rfl := enc_inj_abi hy'
              refine ⟨rfl, rfl, ?_⟩
              funext k
              change BitVec.ofNat 64 (Ascent.AddrMem.read64 sa.mem
                (sa.regs reg + BitVec.ofNat 64 (8 * k.1))).toNat = _
              rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              rfl
      | there v =>
          obtain ⟨b, hb, hs⟩ := slotOK_lookup sa as
            (fun a' ha => h a' (List.mem_cons_of_mem _ ha)) V hV v
          exact ⟨b, hb, hs⟩

/-- **The mapped entry valuation is the one the layout reads off the entry state.** For a
    source environment the layout reads off `sa` and a valuation of the entry parameters
    whose encodings it holds, the mapped valuation satisfies `AbiValOf`. -/
theorem abiValOf_mapVal {σ : AbiLayout} {sa : Ascent.AddrMem.AState} {env : _root_.Hax.Env}
    (hσ : σ.EnvOf sa env) (V : Valuation (entryCtx (abiEntry σ)))
    (hV : EntryVals env (abiEntry σ) V) :
    X86Backend.ExportCertEntry.AbiValOf σ sa (ctMapValD (mapVal V)) := by
  have hrev : abiEntry σ = σ.args.reverse.map fun a => (a.name, abiKindArr a.kind) := by
    simp [abiEntry, abiParamsArr, List.map_reverse]
  have key : ∀ {t : JasminTy} (v : Var (d := jasminDialect)
      (mapCtx ((entryCtx (abiEntry σ)).map catTy)) t),
      ∃ a, σ.args[X86Backend.ExportCertEntry.argIdx v]? = some a ∧
        SlotOK sa a t (v.lookup (ctMapValD (mapVal V))) := by
    revert V
    rw [hrev]
    intro V hV t v
    obtain ⟨a, ha, hs⟩ := slotOK_lookup sa σ.args.reverse
      (fun a ha => hσ.1 a (List.mem_reverse.mp ha)) V hV v
    refine ⟨a, ?_, hs⟩
    have hlt := JasminLsemSimulation.varIndex_lt v
    simp only [mapCtx, entryCtx, List.length_map, List.length_reverse] at hlt
    simp only [X86Backend.ExportCertEntry.argIdx, mapCtx, entryCtx, List.length_map,
      List.length_reverse]
    exact (List.getElem?_reverse hlt).symm.trans ha
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · obtain ⟨a, ha, -⟩ := key v
    simp [ha]
  · obtain ⟨a, ha, hk, hs⟩ := key v
    exact ⟨a, ha, hk, hs⟩
  · obtain ⟨a, ha, hk, hs⟩ := key v
    exact ⟨a, ha, hk, hs⟩

/-- The valuation of the entry parameters whose encodings a source environment the layout
    reads off an entry state holds is in range. -/
theorem inRange_entry {σ : AbiLayout} {sa : Ascent.AddrMem.AState} {env : _root_.Hax.Env}
    (hσ : σ.EnvOf sa env) (V : Valuation (entryCtx (abiEntry σ)))
    (hV : EntryVals env (abiEntry σ) V) :
    ∀ (s : NfTy) (v : Var (entryCtx (abiEntry σ)) s), InRange s (v.lookup V) := by
  have hrev : abiEntry σ = σ.args.reverse.map fun a => (a.name, abiKindArr a.kind) := by
    simp [abiEntry, abiParamsArr, List.map_reverse]
  revert V
  rw [hrev]
  intro V hV
  exact inRange_of_envOf σ.args.reverse (fun a ha => hσ.1 a (List.mem_reverse.mp ha)) V hV

end CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute
