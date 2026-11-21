/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeR3Linked

/-!
# A decidable check of the conditions on the bodies of a module

`NFCallTreeR3Linked.r3FA_of_shape_linked` takes three conditions on the functions of a module:
no parameter of type `int` (`hfp`), each function has a body at its own signature (`hbody`),
and no operation of a body `crateOp` returns for a call takes an integer argument (`hintB`).
The third quantifies over all call signatures, but `crateBody` returns a body only at the
parameter types and the result type of the function (`crateBody_sig`), so the three conditions
are a check on each function of the module.

## Main definitions

* `intArgFreeOpB`: the Bool form of `OpOk IntArgFree`.
* `goodBodiesB`: the check of the three conditions on each function of a module.

## Main results

* `crateBody_sig`: `crateBody` returns a body only at the signature of the function.
* `goodBodiesB_sound`: `goodBodiesB` implies `hfp`, `hbody` and `hintB`.
* `r3FA_of_shape_goodBodies`: `r3FA_of_shape_linked` with `goodBodiesB` in place of the three
  conditions.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCheck

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.NFDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport
open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport.ExportRegions
open CatCrypt.Crypto.SecureCompilation.VIR.CryptoToJasminCom (mapTy)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (RInstr decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesLink (shiftProg)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.Hax.NFToCat
open CatCrypt.Crypto.Hax.ImpToNF (CrateFn entryCtx)
open CatCrypt.Crypto.Hax (HaxModule LinkedFn find?_prep)
open CatCrypt.Crypto.Hax.NFInline (crateOp crateBody)
open CatCrypt.Crypto.SecureCompilation.Haxc.FrontComplete (opsNB)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFToRoute (abiEntry)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.TargetCallTree
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTree (TreeCallEnv)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeExt (leafSig)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeMont (innerHead)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeContract (contractREG)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFProgCallTreeOracle (RuttFA SkipAns TypedAns
  contractRACA)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeFrontModule (OpOk)
open CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCall (IntArgFree opsNB_hasOp)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall

/-- An operation whose leaf call has no argument of type `int`, under any number of names: the
    Bool form of `OpOk IntArgFree`. -/
def intArgFreeOpB : NfOp → Bool
  | .named _ o => intArgFreeOpB o
  | .call _ as _ => decide (NfTy.int ∉ as)
  | _ => true

/-- An operation that passes `intArgFreeOpB` satisfies `OpOk IntArgFree`. -/
theorem opOk_of_intArgFreeOpB : ∀ o : NfOp, intArgFreeOpB o = true → OpOk IntArgFree o := by
  intro o
  induction o with
  | named n o ih => exact ih
  | call f as r => intro h; simpa [intArgFreeOpB, OpOk, IntArgFree] using h
  | _ => intro _; simp [OpOk]

/-- **The check of the conditions on the bodies of a module**: for each function of `m`, no
    parameter has type `int`, the function has a body at its own signature (`crateBody`), and
    no operation of that body takes an argument of type `int`. -/
def goodBodiesB (m : HaxModule) : Bool :=
  m.fns.all fun f =>
    f.params.all (fun p => p.2 != .int) &&
      (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params) f.res
        m.linkSig).any fun b => opsNB intArgFreeOpB b (fun _ => true)

/-- **`crateBody` returns a body at one signature at most**: two bodies of the same function
    have the same parameter types and the same result type. -/
theorem crateBody_sig {fs : List CrateFn} {c : CrateFn} {as as' : List NfTy} {r r' : NfTy}
    {base : String → List NfTy → Option NfTy} {b : NFProg nfDialect as [r]}
    {b' : NFProg nfDialect as' [r']}
    (hb : crateBody fs c as r base = some b) (hb' : crateBody fs c as' r' base = some b') :
    as = as' ∧ r = r' := by
  unfold crateBody at hb hb'
  split at hb
  · rename_i hw
    simp only [hw, ↓reduceIte] at hb'
    obtain ⟨o, ho, hb⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨o', ho', hb'⟩ := Option.bind_eq_some_iff.mp hb'
    rw [ho] at ho'
    cases ho'
    split at hb
    · split at hb'
      · rename_i h h'
        exact ⟨h.1.symm.trans h'.1, h.2.symm.trans h'.2⟩
      · cases hb'
    · cases hb
  · cases hb

/-- **`goodBodiesB` implies the three conditions on the bodies** of
    `NFCallTreeR3Linked.r3FA_of_shape_linked`: `hfp`, `hbody` and `hintB`. -/
theorem goodBodiesB_sound {m : HaxModule} (h : goodBodiesB m = true) :
    (∀ f ∈ m.fns, ∀ p ∈ f.params, p.2 ≠ .int) ∧
    (∀ f ∈ m.fns, (crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params)
      f.res m.linkSig).isSome = true) ∧
    (∀ g as r b, crateOp (m.prepared nfBody) (.call g as r) m.linkSig = some b →
      ∀ o, b.HasOp o → OpOk IntArgFree o) := by
  simp only [goodBodiesB, List.all_eq_true, Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_⟩
  · intro f hf p hp
    have := (h f hf).1 p hp
    simpa using this
  · intro f hf
    exact Option.isSome_of_any (h f hf).2
  · intro g as r b hb o ho
    simp only [crateOp, HaxModule.prepared, find?_prep] at hb
    obtain ⟨fn, hfn, hb⟩ := Option.bind_eq_some_iff.mp hb
    obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp hfn
    have hmem := List.mem_of_find?_eq_some hf
    have h2 := (h f hmem).2
    revert h2
    rcases hc : crateBody (m.prepared nfBody) (f.prep nfBody) (entryCtx f.params) f.res
      m.linkSig with _ | b'
    · simp
    · intro h2
      obtain ⟨rfl, rfl⟩ := crateBody_sig hb hc
      rw [HaxModule.prepared, hb] at hc
      cases hc
      exact opOk_of_intArgFreeOpB o (opsNB_hasOp _ (by simpa using h2) o ho)

/-- **The conclusion of `R3StatementFA TypedAns` at a module, from its shape and the check
    `goodBodiesB`.** The statement of `NFCallTreeR3Linked.r3FA_of_shape_linked` with the
    conditions `hfp`, `hbody` and `hintB` on the functions of the module replaced by
    `goodBodiesB m = true` (`goodBodiesB_sound`). -/
theorem r3FA_of_shape_goodBodies {m : HaxModule} {σ : AbiLayout} {fname : String}
    {P : Lprog} {bytes : List (BitVec 8)} (hc : compileA m σ fname = some (P, bytes))
    (hnd : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hn : narrowOk m σ = false) (hpt : pairTailOf m σ = none)
    (hcf : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg jasminDialect (nfCtx σ) [mapTy (catTy q.1)]), haxToNF σ m = some q →
      (extChain (linkedDecls m CatCrypt.Crypto.Hax.hax64WExit) _ q.1).run q.2
        = some p → p.callFree = false)
    (tE : TreeCallEnv leafSig nfDialect)
    (htE : ∀ (f : String) (as rs : List NfTy) (x : Ctxt.Valuation (d := nfDialect) as),
      tE.call f as rs x = .ret none)
    (hpar : ∀ l ∈ m.linked, (∀ p ∈ l.params, p.2 = .word 64 ∨ p.2 = .int) ∧ l.res = .word 64)
    (hword : ∀ c ∈ m.linked.filterMap LinkedFn.calleeData, (∃ r, c.res = .reg r)
      ∧ c.arrArgs = (fun _ => none) ∧ ∀ a ∈ c.args, X86Backend.DecodePrinted.gpOk a = true)
    (hin : ∀ l ∈ m.linked, innerHead l.name = false)
    (hspine : NFCallTreeInlineSpine.spineArgsOk m.entry.erase = true)
    (hfs : ∀ f ∈ m.fns, NFCallTreeInlineSpine.spineArgsOk f.texpr.erase = true)
    (hint : ∀ (q : Σ t : NfTy, NFProg nfDialect (entryCtx (abiEntry σ)) [t])
      (p : NFProg nfDialect (entryCtx (abiEntry σ)) [q.1]), haxToNF σ m = some q →
      nfSrcProgC (m.prepared nfBody ++ m.linkedFns) σ (bindConsts σ.consts m.entry)
        = some ⟨q.1, p⟩ → ∀ o, p.HasOp o → OpOk IntArgFree o)
    (hgb : goodBodiesB m = true) :
    ∃ (pc Q : List RInstr) (sym : Nat → String),
      decodeLprog bytes = some (pc ++ shiftProg pc.length Q) ∧
      ∀ (sa : AState), σ.Regions sa → ∀ env, σ.EnvOf (narrowEntry m σ sa) env →
        ∀ fuelC fuel,
          RuttFA (SkipAns TypedAns m) (contractREG m) (contractRACA TypedAns m) (resRel σ sa)
            srcFail
            (nfTree (moduleTreeTable m CatCrypt.Crypto.Hax.hax64WExit fuelC) fuel
              m.entry.erase env)
            (fun fuelT => targetTree aMachine pc sym (linkRead m) fuelT 0 sa) :=
  have hs := goodBodiesB_sound hgb
  NFCallTreeR3Linked.r3FA_of_shape_linked hc hnd hk hn hpt hcf tE htE hpar hword hin hspine hfs
    hint hs.1 hs.2.1 hs.2.2

end CatCrypt.Crypto.SecureCompilation.Haxc.NFCallTreeGoodCheck
