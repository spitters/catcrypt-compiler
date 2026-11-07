/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.NFChain
import HaxLean.ByteWords

@[expose] public section

set_option autoImplicit false

/-!
# Narrow parameters cut to their widths at entry

System V leaves the bits of an argument register above the width of a narrower unsigned
parameter unspecified. The source semantics `haxRuns` reads such a parameter at its width
(`narrowEntry`, `AbiLayout.clean`); the chain proves its theorems at the whole registers
(`haxRunsW`). The narrow stage joins the two: it binds each narrow parameter of the entry to
its register cut to its width (`maskArgs`, a binding `let x = x & (2 ^ w - 1)` at entry,
`BitAnd#64` on two `u64` words), and every run that `haxRuns` reads is a run of the stage's
module at the whole registers (`haxRunsW_narrowStage`). The stage adds no pass: the binding is
source code of the module that the front translates as any other.

## Main definitions

* `maskBind`, `maskArgs` — the binding that cuts a parameter to its width, and the bindings of
  every narrow parameter of a layout.
* `narrowStage` — the module whose entry begins with those bindings, under the layout without
  widths; the module and the layout themselves when `narrowOk` fails.

## Main results

* `run_maskArgs` — the bindings run as the cut of the narrow parameters of the environment.
* `haxRunsW_narrowStage` — every source run at the widths is a run of the stage at the whole
  registers, to the same value.
-/

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open _root_.Hax (TExpr Value Env ImpExpr ImpLit Builtins)
open _root_.Hax.InlineLocalClosures (denoteSpine)
open CatCrypt.Crypto.Hax (HaxModule hax64WExit)
open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState)

/-- The binding `let x = x & (2 ^ w - 1)` before `body`: the parameter `x` cut to its low `w`
    bits by `maskCall` on two `u64` words. -/
def maskBind (x : String) (w : Nat) (body : TExpr) : TExpr :=
  .mk (.letBind x (.mk (.app maskCall [.mk (.var x) (.uint .w64),
    .mk (.lit (.int ((2 ^ w - 1 : Nat) : Int))) (.uint .w64)]) (.uint .w64)) body) body.ty

/-- The bindings `maskBind` of each parameter of `as` whose register the layout narrows, in
    parameter order, before `te`. -/
def maskArgs (σ : AbiLayout) : List AbiArg → TExpr → TExpr
  | [], te => te
  | a :: as, te =>
      match σ.widthOf a.reg with
      | some w => maskBind a.name w (maskArgs σ as te)
      | none => maskArgs σ as te

/-- **The narrow stage**: when the narrow parameters are read at their widths (`narrowOk`), the
    module whose entry begins with the bindings `maskArgs` of the parameters of the layout,
    under the layout without widths; the module and the layout otherwise. -/
def narrowStage (m : HaxModule) (σ : AbiLayout) : HaxModule × AbiLayout :=
  if narrowOk m σ then ({ m with entry := maskArgs σ σ.args m.entry }, { σ with widths := [] })
  else (m, σ)

/-- The narrow stage keeps the linked functions of the module. -/
theorem narrowStage_linked (m : HaxModule) (σ : AbiLayout) :
    (narrowStage m σ).1.linked = m.linked := by
  unfold narrowStage
  split <;> rfl

/-- The narrow stage keeps the functions and the depth of the module, so its table. -/
theorem narrowStage_table (m : HaxModule) (σ : AbiLayout) :
    (narrowStage m σ).1.table = m.table := by
  unfold narrowStage
  split <;> rfl

/-- The layout of the narrow stage is the layout with its widths dropped, or the layout. -/
theorem narrowStage_layout (m : HaxModule) (σ : AbiLayout) :
    (narrowStage m σ).2 = σ ∨ (narrowStage m σ).2 = { σ with widths := [] } := by
  unfold narrowStage
  split
  · exact .inr rfl
  · exact .inl rfl

/-- On a layout without narrowed registers the narrow stage is the identity. -/
theorem narrowStage_of_widths_nil {σ : AbiLayout} (h : σ.widths = []) (m : HaxModule) :
    narrowStage m σ = (m, σ) := by
  simp [narrowStage, narrowOk, h]

/-! ## The run of the bindings -/

/-- The value of the cut of an integer word: `maskCall` at the table `hax64WExit`. -/
theorem hax64WExit_mask {n : Nat} (hn : n < 2 ^ 64) {w : Nat} (hw : w ≤ 64) :
    hax64WExit maskCall [.int (n : Int), .int ((2 ^ w - 1 : Nat) : Int)]
      = some (.int ((n % 2 ^ w : Nat) : Int)) := by
  have hm : 2 ^ w - 1 < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos) (Nat.pow_le_pow_right (by omega) hw)
  have hb := _root_.Hax.ByteWords.hax64Builtins_bitAnd_nat hn hm
  rw [Nat.and_two_pow_sub_one_eq_mod] at hb
  rw [CatCrypt.Crypto.Hax.hax64WExit_of_ne (by decide) (by decide) (by decide) (by decide)]
  have hs : ∀ k : Nat, k < 2 ^ 64 → CatCrypt.Crypto.Hax.scalarValNB (.int (k : Int)) = true := by
    intro k hk
    simp only [CatCrypt.Crypto.Hax.scalarValNB, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hr : n % 2 ^ w < 2 ^ 64 := lt_of_le_of_lt (Nat.mod_le _ _) hn
  have hop : CatCrypt.Crypto.Hax.hax64ScalarOp maskCall = true := by
    simp [maskCall, CatCrypt.Crypto.Hax.hax64ScalarOp, CatCrypt.Crypto.Hax.scalarOpExprT,
      CatCrypt.Crypto.Hax.widthOpOf]
  have hto : CatCrypt.Crypto.Hax.towerOfCallName maskCall = .TFp := by
    simp [maskCall, CatCrypt.Crypto.Hax.towerOfCallName,
      CatCrypt.Crypto.Hax.TowerOfCallNameInst.callTower,
      CatCrypt.Crypto.Hax.towerOfCallName_default]
  have hres : CatCrypt.Crypto.Hax.exitScalarRes maskCall = true := by
    simp [maskCall, CatCrypt.Crypto.Hax.exitScalarRes, CatCrypt.Crypto.Hax.exitScalarCall]
  have hne : (maskCall != "len") = true := by simp [maskCall]
  refine CatCrypt.Crypto.Hax.hax64Exit_of_scalarAdmit hb rfl ?_
  simp only [CatCrypt.Crypto.Hax.hax64ScalarAdmit, hres, hne, CatCrypt.Crypto.Hax.hax64ArgsShape,
    hop, hto, hs _ hr, ite_true, List.length_cons, List.length_nil, List.all_cons, List.all_nil,
    hs _ hn, hs _ hm, Bool.and_true, Bool.true_and, beq_self_eq_true]
  simp only [CatCrypt.Crypto.Hax.exitMarshalOk, CatCrypt.Crypto.Jasmin.LowCT.TowerType.storageBytes]
  decide

/-- The relation of an environment before the bindings `maskArgs σ L` to the environment after
    them: at the name of a parameter of `L` whose register `σ` narrows to `w` bits the first
    holds an integer word `n` and the second its cut `n % 2 ^ w`; at every other name they
    agree. -/
def MaskRel (σ : AbiLayout) (L : List AbiArg) (E E' : Env) : Prop :=
  ∀ y, (∀ a ∈ L, ∀ w, a.name = y → σ.widthOf a.reg = some w →
      ∃ n : Nat, n < 2 ^ 64 ∧ E y = some (.int (n : Int))
        ∧ E' y = some (.int ((n % 2 ^ w : Nat) : Int)))
    ∧ ((∀ a ∈ L, a.name = y → σ.widthOf a.reg = none) → E y = E' y)

/-- **The bindings run as the cut of the narrow parameters.** At a table that answers
    `maskCall` on integer words as `hax64WExit`, for parameters with distinct names whose
    widths are at most `64`, the reading of `maskArgs σ L te` from `E` is the reading of `te`
    from an environment `E'` in `MaskRel` with `E`. -/
theorem run_maskArgs {σ : AbiLayout} {bi : Builtins}
    (hbi : ∀ vals, bi maskCall vals = hax64WExit maskCall vals) (fuel : Nat) (te : TExpr) :
    ∀ (L : List AbiArg), (L.map (·.name)).Nodup →
      (∀ a ∈ L, ∀ w, σ.widthOf a.reg = some w → w ≤ 64) →
      ∀ (E E' : Env), MaskRel σ L E E' →
        (denoteSpine bi fuel (maskArgs σ L te).erase).run E =
          (denoteSpine bi fuel te.erase).run E'
  | [], _, _, E, E', h => by
      have : E = E' := funext fun y => (h y).2 fun a ha => by simp at ha
      subst this
      rfl
  | a :: as, hnd, hw, E, E', h => by
      have hnd2 := List.nodup_cons.mp (show (a.name :: as.map (·.name)).Nodup from hnd)
      have hnd' := hnd2.2
      have hnot : ∀ b ∈ as, b.name ≠ a.name := fun b hb he =>
        hnd2.1 (he ▸ List.mem_map_of_mem (f := (·.name)) hb)
      have hw' : ∀ b ∈ as, ∀ w, σ.widthOf b.reg = some w → w ≤ 64 :=
        fun b hb => hw b (List.mem_cons_of_mem _ hb)
      cases hwa : σ.widthOf a.reg with
      | none =>
          simp only [maskArgs, hwa]
          refine run_maskArgs hbi fuel te as hnd' hw' E E' fun y => ⟨?_, ?_⟩
          · exact fun b hb => (h y).1 b (List.mem_cons_of_mem _ hb)
          · intro hy
            refine (h y).2 fun b hb hby => ?_
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hwa
            · exact hy b hb hby
      | some w =>
          obtain ⟨n, hn, hE, hE'⟩ := (h a.name).1 a List.mem_cons_self w rfl hwa
          have hw0 : w ≤ 64 := hw a List.mem_cons_self w hwa
          simp only [maskArgs, hwa]
          have hb : ∀ {α β : Type} (m : StateM Env α) (f : α → StateM Env β) (s : Env),
              (m >>= f) s = f (m s).1 (m s).2 := fun _ _ _ => rfl
          have hg : ∀ (s : Env), (get : StateM Env Env) s = (s, s) := fun _ => rfl
          have hp : ∀ {α : Type} (x : α) (s : Env), (pure x : StateM Env α) s = (x, s) :=
            fun _ _ => rfl
          have hmod : ∀ (f : Env → Env) (s : Env), (modify f : StateM Env PUnit) s = (⟨⟩, f s) :=
            fun _ _ => rfl
          have hmask : bi maskCall [.int (n : Int), .int ((2 ^ w - 1 : Nat) : Int)]
              = some (.int ((n % 2 ^ w : Nat) : Int)) := by
            rw [hbi, hax64WExit_mask hn hw0]
          change denoteSpine bi fuel (.letBind a.name (.app maskCall [.var a.name,
            .lit (.int ((2 ^ w - 1 : Nat) : Int))]) (maskArgs σ as te).erase) E = _
          simp only [denoteSpine, _root_.Hax.denote', _root_.Hax.denoteApp',
            _root_.Hax.denoteArgs', hb, hg, hp, hmod, hE, _root_.Hax.Value.ofLit, hmask,
            Option.map]
          refine run_maskArgs hbi fuel te as hnd' hw' _ E' fun y => ⟨?_, ?_⟩
          · intro b hb' w' hby hbw
            have hya : y ≠ a.name := hby ▸ hnot b hb'
            obtain ⟨n', hn', h1, h2⟩ := (h y).1 b (List.mem_cons_of_mem _ hb') w' hby hbw
            refine ⟨n', hn', ?_, h2⟩
            simp [_root_.Hax.Env.extend, hya, h1]
          · intro hy
            by_cases hya : y = a.name
            · subst hya
              simp [_root_.Hax.Env.extend, hE']
            · rw [show _root_.Hax.Env.extend E a.name _ y = E y by
                simp [_root_.Hax.Env.extend, hya]]
              refine (h y).2 fun b hb hby => ?_
              rcases List.mem_cons.mp hb with rfl | hb
              · exact absurd hby.symm hya
              · exact hy b hb hby

/-! ## The source run through the narrow stage -/

/-- The table of a module answers `maskCall` as its base table when no function and no linked
    function of the module has that name. -/
theorem table_mask {m : HaxModule} (hf : m.fns.all (·.name != maskCall) = true)
    (hl : m.linked.all (·.name != maskCall) = true) (bi : Builtins) (fuelC : Nat)
    (vals : List Value) : m.table bi fuelC maskCall vals = bi maskCall vals := by
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at hf hl
  rw [HaxModule.table, CatCrypt.Crypto.Hax.refBi_of_find_none, HaxModule.linkTable,
    CatCrypt.Crypto.Hax.linkBi_of_find_none]
  · exact List.find?_eq_none.mpr fun l h => by simpa using hl l h
  · exact List.find?_eq_none.mpr fun f h => by simpa using hf f h

/-- The data of `narrowOk`. -/
theorem narrowOk_spec {m : HaxModule} {σ : AbiLayout} (h : narrowOk m σ = true) :
    (∀ p ∈ σ.widths, p.2 ≤ 64 ∧ ∀ a ∈ σ.args, a.reg = p.1 → a.kind = .scalar)
      ∧ (σ.args.map (·.name)).Nodup ∧ (∀ c ∈ σ.consts, ∀ a ∈ σ.args, a.name ≠ c.1)
      ∧ m.fns.all (·.name != maskCall) = true ∧ m.linked.all (·.name != maskCall) = true := by
  simp only [narrowOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.any_eq_false, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨-, hw⟩, hnd⟩, hc⟩, hf⟩, hl⟩ := h
  refine ⟨fun p hp => ⟨(hw p hp).1, fun a ha hr => ?_⟩, hnd, fun c hc' a ha hn => hc c hc' a ha hn,
    by simpa using hf, by simpa using hl⟩
  rcases (hw p hp).2 a ha with h | h
  · exact absurd hr h
  · exact h

/-- A register the layout narrows is listed in its widths, with a width of the list. -/
theorem mem_widths_of_widthOf {σ : AbiLayout} {r : String} {w : Nat}
    (h : σ.widthOf r = some w) : (r, w) ∈ σ.widths := by
  unfold AbiLayout.widthOf at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have := List.find?_some hp
  have hr : p.1 = r := by simpa using this
  exact hr ▸ List.mem_of_find?_eq_some hp

/-- **The source run through the narrow stage.** Every source run of `m` from `sa` to `v` under
    `σ` that reads each narrow parameter at its width (`haxRuns`) is a run of the module of the
    narrow stage under its layout at the whole registers (`haxRunsW`), to the same value: the
    environment that binds each narrow parameter to its whole register runs the bindings
    `maskArgs` to the environment of the run (`run_maskArgs`). -/
theorem haxRunsW_narrowStage {m : HaxModule} {σ : AbiLayout} {sa : AState} {v : Value}
    (hrun : haxRuns σ m sa v) : haxRunsW (narrowStage m σ).2 (narrowStage m σ).1 sa v := by
  unfold haxRuns narrowEntry at hrun
  unfold narrowStage
  split
  · rename_i hok
    rw [ite_eq_left hok] at hrun
    obtain ⟨hwid, hnd, hcs, hf, hl⟩ := narrowOk_spec hok
    obtain ⟨env, fuel, fuelC, env', ⟨hA, hC, hN⟩, hr, hcf⟩ := hrun
    -- the environment of the whole registers
    let nar : AbiArg → Bool := fun a => (σ.widthOf a.reg).isSome
    let env₀ : Env := fun y =>
      match σ.args.find? (fun a => a.name == y && nar a) with
      | some a => some (a.read sa)
      | none => env y
    have huniq : ∀ a ∈ σ.args, ∀ b ∈ σ.args, a.name = b.name → a = b := by
      intro a ha b hb hab
      exact List.inj_on_of_nodup_map hnd ha hb hab
    have hfind : ∀ a ∈ σ.args, nar a = true →
        σ.args.find? (fun b => b.name == a.name && nar b) = some a := by
      intro a ha hn
      have hs : (σ.args.find? (fun b => b.name == a.name && nar b)).isSome := by
        rw [List.find?_isSome]; exact ⟨a, ha, by simp [hn]⟩
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hs
      have hb' := List.find?_some hb
      simp only [Bool.and_eq_true, beq_iff_eq] at hb'
      rw [hb, huniq b (List.mem_of_find?_eq_some hb) a ha hb'.1]
    have hfind0 : ∀ y, (∀ a ∈ σ.args, a.name = y → nar a = false) →
        σ.args.find? (fun b => b.name == y && nar b) = none := by
      intro y hy
      exact List.find?_eq_none.mpr fun b hb hb' => by
        simp only [Bool.and_eq_true, beq_iff_eq] at hb'
        rw [hy b hb hb'.1] at hb'
        exact Bool.false_ne_true hb'.2
    have henv₀ : σ.EnvOf sa env₀ := by
      refine ⟨fun a ha => ?_, fun c hc => ?_, fun y hy => ?_⟩
      · cases hn : nar a
        · have h0 := hfind0 a.name fun b hb hab => huniq b hb a ha hab ▸ hn
          simp only [env₀, h0, hA a ha]
          have hw : σ.widthOf a.reg = none := by simpa [nar] using hn
          rw [AbiLayout.read_clean_of_none hw]
        · simp only [env₀, hfind a ha hn]
      · have h0 := hfind0 c.1 fun b hb hbc => absurd hbc (hcs c hc b hb)
        simp only [env₀, h0, hC c hc]
      · simp only [env₀] at hy
        split at hy
        · rename_i b hb
          have hb' := List.find?_some hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hb'
          exact List.mem_append_left _ (hb'.1 ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hb))
        · exact hN y hy
    have hrel : MaskRel σ σ.args env₀ env := by
      intro y
      refine ⟨fun a ha w hay haw => ?_, fun hy => ?_⟩
      · have hn : nar a = true := by simp [nar, haw]
        have hk : a.kind = .scalar := (hwid _ (mem_widths_of_widthOf haw)).2 a ha rfl
        refine ⟨(sa.regs a.reg).toNat, (sa.regs a.reg).isLt, ?_, ?_⟩
        · subst hay
          simp only [env₀, hfind a ha hn, AbiArg.read, hk]
        · subst hay
          rw [hA a ha, AbiLayout.read_clean_of_width hk haw]
      · have h0 := hfind0 y fun b hb hby => by simpa [nar] using hy b hb hby
        simp only [env₀, h0]
    have hbi : ∀ vals, m.table hax64WExit fuelC maskCall vals = hax64WExit maskCall vals :=
      table_mask hf hl hax64WExit fuelC
    have hw64 : ∀ a ∈ σ.args, ∀ w, σ.widthOf a.reg = some w → w ≤ 64 :=
      fun a _ w h => (hwid _ (mem_widths_of_widthOf h)).1
    refine ⟨env₀, fuel, fuelC, env', henv₀, ?_, hcf⟩
    change (denoteSpine (m.table hax64WExit fuelC) fuel (maskArgs σ σ.args m.entry).erase).run
      env₀ = _
    rw [run_maskArgs hbi fuel m.entry σ.args hnd hw64 env₀ env hrel]
    exact hr
  · rename_i hok
    rw [ite_eq_right hok] at hrun
    exact hrun

end CatCrypt.Crypto.SecureCompilation.Haxc
