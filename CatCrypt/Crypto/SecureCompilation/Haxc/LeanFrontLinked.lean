/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.LeanFront
public import CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall
public import CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked

/-!
# Compiled bytes of a reified Lean function with linked kernels

`leanFront_correct` states the correctness of `compileA` on the module of a single function,
which has no linked function. This module states it on a module `m` whose linked functions are
linked kernels (`RegionLinkCall.LinkedKernel`) with distinct names, the hypotheses of
`haxc_correct_auto`. The ascent result is taken under the table `m.table hax64WExit fuelC` of
the module, at which a call of a linked function is the value of its meaning. On the module of
an entry `te` with no callee and the linked functions `ls`, that table is
`linkBi ls hax64WExit` (`table_entryLinked`).

The decoded program either halts at the address machine (`Halts`) or, when it calls a linked
kernel, halts through the calls (`HaltsC`); in both cases `σ` reads back the encoding of `f a`.

## Main results

* `haxRuns_of_fnCorres` — an ascent result under the table of a module gives a source run of
  the module (`haxRuns`), the hypothesis of `haxc_correct_auto`.
* `leanFront_correct_linked`, `leanFront_correct_linked_scalar`,
  `leanFront_correct_linked_words` — `leanFront_correct` and its scalar and word-array forms at
  a module with linked kernels.
* `table_entryLinked` — the table of the module of an entry and linked functions.
* `leanFront_correct_sha512` — the hypotheses on the linked functions hold at the module of an
  entry linking the SHA-512 compression `Sha2Linked.sha512Kernel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.VIR.JasminLprogExport (Lprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.LprogBytesDecode (decodeLprog)
open CatCrypt.Crypto.SecureCompilation.X86Backend.RInstrSemantics (Halts HaltsC)
open CatCrypt.Crypto.SecureCompilation.Ascent.RInstrAddrMem (aMachine)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)
open CatCrypt.Crypto.SecureCompilation.Haxc.RegionLinkCall (LinkedKernel)
open CatCrypt.Crypto.Hax (hax64WExit spineLamFree HaxModule LinkedFn linkBi refBi refBi_nil)
open _root_.Hax (TExpr Value Env denote')
open _root_.Hax.InlineLocalClosures (denoteSpine)
open _root_.Hax.Ascent (FnCorres HaxEnc enc bindParams)

/-- **An ascent result gives a source run of a module.** Let the statement spine of the entry
    of `m` bind no closure and let the entry from `bindParams (ps a)` return the encoding of
    `f a` under the table `m.table hax64WExit fuelC` for every argument in the guard. From an
    entry state `sa` whose canonical environment is `bindParams (ps a)`, on a layout whose
    narrow parameters are not cut to their widths, the module runs to the encoding of
    `f a` (`haxRuns`). -/
theorem haxRuns_of_fnCorres {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (m : HaxModule)
    (σ : AbiLayout) (fuelC : Nat) (hsp : spineLamFree m.entry.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres (m.table hax64WExit fuelC) m.entry.erase (fun a => bindParams (ps a)) G f)
    (hnd : σ.envNames.Nodup) (sa : AState) (a : A) (hG : G a)
    (hcanon : σ.canonEnv sa = bindParams (ps a)) (hn : narrowOk m σ = false) :
    haxRuns σ m sa (enc (f a)) := by
  have he : narrowEntry m σ sa = sa := by simp [narrowEntry, hn]
  obtain ⟨fuel, hr⟩ := hf a hG
  have henv : σ.EnvOf sa (bindParams (ps a)) := hcanon ▸ σ.envOf_canonEnv hnd sa
  refine ⟨bindParams (ps a), fuel, fuelC,
    (denote' (m.table hax64WExit fuelC) fuel m.entry.erase (bindParams (ps a))).2,
    by rw [he]; exact henv, ?_, HaxEnc.Plain.not_cf (f a)⟩
  rw [denoteSpine_eq_denote' _ _ _ hsp]
  exact Prod.ext (hr fuel (Nat.le_refl fuel)) rfl

/-- **Compiled bytes compute the function of an ascent result, with linked kernels.** Let the
    linked functions of `m` have distinct names (`hndL`) and each be a linked kernel (`hk`),
    let `compileA` return `(P, bytes)` on `m` under the layout `σ`, whose names are pairwise
    distinct, and let the entry of `m` correspond to `f` under the table of `m` (`FnCorres`).
    From every entry state `sa` satisfying `σ.Regions` whose canonical environment is
    `bindParams (ps a)` for an argument `a` in the guard, the bytes decode to a program that
    halts, at the address machine or through its calls of linked kernels, in a state from which
    `σ` reads back the encoding of `f a`. -/
theorem leanFront_correct_linked {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (m : HaxModule)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes)) (fuelC : Nat)
    (hsp : spineLamFree m.entry.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres (m.table hax64WExit fuelC) m.entry.erase (fun a => bindParams (ps a)) G f)
    (hndL : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (a : A) (hG : G a)
    (hcanon : σ.canonEnv sa = bindParams (ps a)) (hn : narrowOk m σ = false := by rfl) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a)))
        ∨ ∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a))) := by
  obtain ⟨prog, hd, h⟩ := haxc_correct_auto m σ fname P bytes hc sa hsep _
    (haxRuns_of_fnCorres m σ fuelC hsp ps G f hf hnd sa a hG hcanon hn) hndL hk
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, hC, -⟩
  · exact .inl ⟨sa', hh, hR⟩
  · exact .inr hC

/-- **Compiled bytes compute the function of an ascent result, scalar layout, with linked
    kernels.** The statement of `leanFront_correct_linked` for a layout whose parameters are
    `u64` scalars and which binds no constant. -/
theorem leanFront_correct_linked_scalar {A β : Type} [HaxEnc β] [HaxEnc.Plain β]
    (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes)) (fuelC : Nat)
    (hsp : spineLamFree m.entry.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres (m.table hax64WExit fuelC) m.entry.erase (fun a => bindParams (ps a)) G f)
    (hndL : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hs : ∀ a ∈ σ.args, a.kind = .scalar) (hconsts : σ.consts = [])
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (a : A) (hG : G a)
    (hregs : σ.args.map (fun x => (x.name, Value.int (sa.regs x.reg).toNat)) = ps a)
    (hn : narrowOk m σ = false := by rfl) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a)))
        ∨ ∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a))) :=
  leanFront_correct_linked m σ fname P bytes hc fuelC hsp ps G f hf hndL hk hnd sa hsep a hG
    (by rw [canonEnv_eq_bindParams σ hs hconsts sa, hregs]) hn

/-- **Compiled bytes compute the function on two word arrays, with linked kernels.** The
    statement of `leanFront_correct_words` at a module with linked kernels: for a layout with
    two word-array parameters and the result read back as the `N` words at the entry address
    in `%rdi`, the result words of the halting state are the encoding of `f (x, y, ())`. -/
theorem leanFront_correct_linked_words {α β : Type} [HaxEnc α] [HaxEnc β] [HaxEnc.Plain β]
    (m : HaxModule) (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA m σ fname = some (P, bytes)) (fuelC : Nat)
    (hsp : spineLamFree m.entry.erase = true)
    (xn yn rx ry : String) (n₁ n₂ N : Nat)
    (hargs : σ.args = [⟨xn, rx, .words n₁⟩, ⟨yn, ry, .words n₂⟩]) (hconsts : σ.consts = [])
    (hres : σ.result = .words "%rdi" N)
    (G : Array α × (Array α × Unit) → Prop) (f : Array α × (Array α × Unit) → β)
    (hf : FnCorres (m.table hax64WExit fuelC) m.entry.erase
      (fun a => bindParams [(xn, enc a.1), (yn, enc a.2.1)]) G f)
    (hndL : (m.linked.map (·.name)).Nodup) (hk : ∀ l ∈ m.linked, LinkedKernel l)
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (x y : Array α)
    (hx : wordsAt sa.mem (sa.regs rx) n₁ = x.toList.map enc)
    (hy : wordsAt sa.mem (sa.regs ry) n₂ = y.toList.map enc) (hG : G (x, y, ()))
    (hn : narrowOk m σ = false := by rfl) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa'
          ∧ enc (f (x, y, ())) = .array (wordsAt sa'.mem (sa.regs "%rdi") N))
        ∨ ∃ sa', HaltsC aMachine prog 0 sa sa'
          ∧ enc (f (x, y, ())) = .array (wordsAt sa'.mem (sa.regs "%rdi") N)) := by
  have hback : ∀ sa', σ.ResultOf sa sa' (enc (f (x, y, ()))) →
      enc (f (x, y, ())) = .array (wordsAt sa'.mem (sa.regs "%rdi") N) := by
    intro sa' hR
    unfold AbiLayout.ResultOf at hR
    rw [hR, hres]
    rfl
  obtain ⟨prog, hd, h⟩ := leanFront_correct_linked m σ fname P bytes hc fuelC hsp
    (fun a => [(xn, enc a.1), (yn, enc a.2.1)]) G f hf hndL hk hnd sa hsep (x, y, ()) hG (by
      rw [canonEnv_eq_bindParams_read σ hconsts sa, hargs]
      simp only [List.map_cons, List.map_nil, AbiArg.read, hx, hy]
      rfl) hn
  refine ⟨prog, hd, ?_⟩
  rcases h with ⟨sa', hh, hR⟩ | ⟨sa', hh, hR⟩
  · exact .inl ⟨sa', hh, hback sa' hR⟩
  · exact .inr ⟨sa', hh, hback sa' hR⟩

/-- **The table of the module of an entry and linked functions**: on the module with the entry
    `te`, no callee, depth `0` and the linked functions `ls`, the table is `linkBi ls bi` at
    every fuel of the callees. -/
theorem table_entryLinked (te : TExpr) (ls : List LinkedFn) (bi : _root_.Hax.Builtins)
    (fuelC : Nat) :
    (⟨te, [], 0, ls⟩ : HaxModule).table bi fuelC = linkBi ls bi := by
  rw [HaxModule.table, refBi_nil]
  rfl

open CatCrypt.Crypto.SecureCompilation.HashTemplate.Sha2Linked (sha512Kernel sha512Kernel_linked)
in
/-- **The Lean front with the SHA-512 compression linked.** On the module of an entry `te`
    with no callee and the one linked function `Sha2Linked.sha512Kernel`, the hypotheses of
    `leanFront_correct_linked` on the linked functions hold (`sha512Kernel_linked`), and the
    ascent result is taken under `linkBi [sha512Kernel] hax64WExit`, at which a call of the
    kernel is the value of the reference compression. -/
theorem leanFront_correct_sha512 {A β : Type} [HaxEnc β] [HaxEnc.Plain β] (te : TExpr)
    (σ : AbiLayout) (fname : String) (P : Lprog) (bytes : List (BitVec 8))
    (hc : compileA ⟨te, [], 0, [sha512Kernel]⟩ σ fname = some (P, bytes))
    (hsp : spineLamFree te.erase = true)
    (ps : A → List (String × Value)) (G : A → Prop) (f : A → β)
    (hf : FnCorres (linkBi [sha512Kernel] hax64WExit) te.erase (fun a => bindParams (ps a)) G f)
    (hnd : σ.envNames.Nodup) (sa : AState) (hsep : σ.Regions sa) (a : A) (hG : G a)
    (hcanon : σ.canonEnv sa = bindParams (ps a))
    (hn : narrowOk ⟨te, [], 0, [sha512Kernel]⟩ σ = false) :
    ∃ prog, decodeLprog bytes = some prog ∧
      ((∃ sa', Halts aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a)))
        ∨ ∃ sa', HaltsC aMachine prog 0 sa sa' ∧ σ.ResultOf sa sa' (enc (f a))) :=
  leanFront_correct_linked ⟨te, [], 0, [sha512Kernel]⟩ σ fname P bytes hc 0 hsp ps G f
    (by rw [table_entryLinked]; exact hf) (List.nodup_singleton _)
    (fun l hl => by rw [List.mem_singleton.mp hl]; exact sha512Kernel_linked)
    hnd sa hsep a hG hcanon hn

end CatCrypt.Crypto.SecureCompilation.Haxc
