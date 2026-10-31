/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.Haxc.AbiLayout
public import HaxAscent.Ascent.Builtins

/-!
# Entry states of a layout and the decoding of its read-back

An `AbiLayout` reads a source environment off an entry state (`AbiLayout.EnvOf`) and a result
off an exit state (`AbiLayout.ResultOf`). This module gives the converse direction of the
entry: `AbiLayout.encodeEntry σ s0 env` is the state `s0` with the word of each scalar
parameter of `env` in its register and the words of each array parameter of `env` stored at the
address its register holds in `s0`. From a base state satisfying `σ.Regions`, the encoded state
satisfies `σ.Regions` and `σ` reads `env` back off it, when every parameter value fits its kind
(`AbiArg.Fits`), the parameter registers are distinct, and no region wraps around the address
space.

The read-back of a result is decoded by `decodeEnc`, the value of a type with an injective
encoding whose encoding is the read-back value.

## Main results

* `AbiArg.Fits` — a value is carried by a parameter without loss.
* `writeWords`, `read64_writeWords_of_disjoint`, `read64_writeWords_mem` — a sequence of word
  stores at pairwise disjoint addresses, and the words read after it.
* `AbiLayout.encodeEntry` — the entry state of a layout for an environment.
* `AbiLayout.regions_encodeEntry`, `AbiLayout.envOf_encodeEntry` — the encoded state satisfies
  the entry conditions of the layout, and the layout reads the environment off it.
* `decodeEnc`, `decodeEnc_enc`, `decodeEnc_resultOf` — the decoding of a read-back value.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Haxc

open CatCrypt.Crypto.SecureCompilation.Ascent.AddrMem (AState AMem read64 write64 Disjoint8
  read64_write64_same read64_write64_of_disjoint Disjoint8.symm)
open _root_.Hax (Value Env)
open _root_.Hax.Ascent (HaxEnc)

/-- The 64-bit word a source integer denotes, modulo `2^64`; `0` for the other values. -/
def valWord : Value → BitVec 64
  | .int n => BitVec.ofInt 64 n
  | _ => 0

/-- Entry `j` of an array value as a word; `0` past its end and for the other values. -/
def valWordAt (v : Value) (j : Nat) : BitVec 64 :=
  match v with
  | .array vs => valWord (vs.getD j (.int 0))
  | _ => 0

/-- The value `v` is carried by the parameter `a` without loss: for a scalar, `v` is the
    integer of its word; for an array of `n` words, `v` is the array of the integers of its
    first `n` words. -/
def AbiArg.Fits (a : AbiArg) (v : Value) : Prop :=
  match a.kind with
  | .scalar => v = .int (valWord v).toNat
  | .words n => v = .array ((List.range n).map fun j => .int (valWordAt v j).toNat)

/-! ## Word stores -/

/-- Store the words of a list of address and word pairs, in list order. -/
def writeWords (m : AMem) (ws : List (BitVec 64 × BitVec 64)) : AMem :=
  ws.foldl (fun m w => write64 m w.1 w.2) m

/-- The unfolding of `writeWords` at a nonempty list. -/
theorem writeWords_cons (m : AMem) (w : BitVec 64 × BitVec 64)
    (ws : List (BitVec 64 × BitVec 64)) :
    writeWords m (w :: ws) = writeWords (write64 m w.1 w.2) ws := rfl

/-- Stores at addresses disjoint from `b` leave the word at `b` unchanged. -/
theorem read64_writeWords_of_disjoint (m : AMem) (ws : List (BitVec 64 × BitVec 64))
    (b : BitVec 64) (h : ∀ w ∈ ws, Disjoint8 w.1 b) :
    read64 (writeWords m ws) b = read64 m b := by
  induction ws generalizing m with
  | nil => rfl
  | cons w ws ih =>
    rw [writeWords_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      read64_write64_of_disjoint _ _ _ _ (h w List.mem_cons_self)]

/-- After stores at pairwise disjoint addresses, the word at a stored address is the word
    stored there. -/
theorem read64_writeWords_mem (m : AMem) (ws : List (BitVec 64 × BitVec 64))
    (h : ws.Pairwise fun x y => Disjoint8 x.1 y.1) {b v : BitVec 64} (hm : (b, v) ∈ ws) :
    read64 (writeWords m ws) b = v := by
  induction ws generalizing m with
  | nil => simp at hm
  | cons w ws ih =>
    rw [writeWords_cons]
    obtain ⟨hw, hp⟩ := List.pairwise_cons.1 h
    rcases List.mem_cons.1 hm with rfl | hm
    · rw [read64_writeWords_of_disjoint _ _ _ (fun x hx => (hw x hx).symm),
        read64_write64_same]
    · exact ih _ hp hm

/-- Two words of one region of at most `2^61` words are disjoint. -/
theorem disjoint8_words (B : BitVec 64) {j k n : Nat} (hj : j < n) (hk : k < n)
    (hn : 8 * n ≤ 2 ^ 64) (h : j ≠ k) :
    Disjoint8 (B + BitVec.ofNat 64 (8 * j)) (B + BitVec.ofNat 64 (8 * k)) := by
  have := B.isLt
  simp only [Disjoint8, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## The entry state of a layout -/

namespace AbiLayout

/-- The pointer regions of a layout, each with the value `env` binds to its parameter. -/
def regionVals (σ : AbiLayout) (env : Env) : List ((String × Nat) × Value) :=
  σ.args.filterMap fun a => a.region.map fun p => (p, (env a.name).getD .unit)

/-- The regions of `regionVals` are the pointer regions of the layout. -/
theorem regionVals_map_fst (σ : AbiLayout) (env : Env) :
    (σ.regionVals env).map Prod.fst = σ.regions := by
  simp only [regionVals, regions, List.map_filterMap, Option.map_map]
  congr 1
  funext a
  cases a.region <;> rfl

/-- The word stores that lay out the arrays of `env` at the regions of `s0`: word `j` of the
    parameter of the region `(r, n)` at `s0.regs r + 8 j`, for `j < n`. -/
def entryWrites (σ : AbiLayout) (s0 : AState) (env : Env) : List (BitVec 64 × BitVec 64) :=
  (σ.regionVals env).flatMap fun pv =>
    (List.range pv.1.2).map fun j => (s0.regs pv.1.1 + BitVec.ofNat 64 (8 * j), valWordAt pv.2 j)

/-- The register file of the entry state: the register of a scalar parameter holds the word of
    its value in `env`, every other register its value in `s0`. -/
def entryRegs (σ : AbiLayout) (s0 : AState) (env : Env) : String → BitVec 64 := fun r =>
  match σ.args.find? (fun a => a.reg == r && a.kind == .scalar) with
  | some a => valWord ((env a.name).getD .unit)
  | none => s0.regs r

/-- **The entry state of the layout `σ` for the environment `env`**: the state `s0` with the
    word of each scalar parameter in its register and the words of each array parameter
    stored at the address its register holds in `s0`. -/
def encodeEntry (σ : AbiLayout) (s0 : AState) (env : Env) : AState :=
  { regs := σ.entryRegs s0 env, flags := s0.flags,
    mem := writeWords s0.mem (σ.entryWrites s0 env) }

/-- Two members of a list of parameters with distinct registers and the same register are
    equal. -/
theorem eq_of_reg_eq : ∀ {l : List AbiArg}, (l.map (·.reg)).Nodup → ∀ {a b : AbiArg},
    a ∈ l → b ∈ l → a.reg = b.reg → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: l, h, a, b, ha, hb, e => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd ⟨b, hb', e.symm⟩ h.1
    · exact absurd ⟨a, ha', e⟩ h.1
    · exact eq_of_reg_eq h.2 ha' hb' e

/-- The register of a scalar parameter holds the word of its value. -/
theorem entryRegs_scalar {σ : AbiLayout} (s0 : AState) (env : Env)
    (hreg : (σ.args.map (·.reg)).Nodup) {a : AbiArg} (ha : a ∈ σ.args)
    (hk : a.kind = .scalar) :
    σ.entryRegs s0 env a.reg = valWord ((env a.name).getD .unit) := by
  unfold entryRegs
  have hs : (σ.args.find? fun a' => a'.reg == a.reg && a'.kind == .scalar).isSome :=
    List.find?_isSome.2 ⟨a, ha, by simp [hk]⟩
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 hs
  have hp := List.find?_some ha'
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  rw [ha', eq_of_reg_eq hreg (List.mem_of_find?_eq_some ha') ha hp.1]

/-- A register that carries no scalar parameter keeps its value. -/
theorem entryRegs_of_not_scalar {σ : AbiLayout} (s0 : AState) (env : Env) {r : String}
    (hr : ∀ a ∈ σ.args, a.reg = r → a.kind ≠ .scalar) :
    σ.entryRegs s0 env r = s0.regs r := by
  unfold entryRegs
  rw [List.find?_eq_none.2 (by grind)]

/-- Under distinct parameter registers, the register of a pointer region keeps its value. -/
theorem entryRegs_region {σ : AbiLayout} (s0 : AState) (env : Env)
    (hreg : (σ.args.map (·.reg)).Nodup) {p : String × Nat} (hp : p ∈ σ.regions) :
    σ.entryRegs s0 env p.1 = s0.regs p.1 := by
  obtain ⟨a, ha, hr⟩ := List.mem_filterMap.1 hp
  unfold AbiArg.region at hr
  split at hr
  · cases hr
  · rename_i n hk
    cases hr
    refine entryRegs_of_not_scalar s0 env fun a' ha' he => ?_
    rw [eq_of_reg_eq hreg ha' ha he, hk]
    nofun

/-- The stores of the entry state are at pairwise disjoint addresses. -/
theorem entryWrites_pairwise {σ : AbiLayout} {s0 : AState} (env : Env) (hs0 : σ.Regions s0)
    (hn : ∀ p ∈ σ.regions, 8 * p.2 ≤ 2 ^ 64) :
    (σ.entryWrites s0 env).Pairwise fun x y => Disjoint8 x.1 y.1 := by
  have hR : σ.regions.Pairwise fun p q => ∀ k k', k < p.2 → k' < q.2 →
      Disjoint8 (s0.regs p.1 + BitVec.ofNat 64 (8 * k))
        (s0.regs q.1 + BitVec.ofNat 64 (8 * k')) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    exact hs0.2.1 i j _ _ (Nat.ne_of_lt hij) (List.getElem?_eq_getElem hi)
      (List.getElem?_eq_getElem hj)
  rw [← regionVals_map_fst σ env, List.pairwise_map] at hR
  unfold entryWrites
  rw [List.pairwise_flatMap]
  refine ⟨fun pv hpv => ?_, hR.imp fun h x hx y hy => ?_⟩
  · have hpv' : pv.1 ∈ σ.regions := by
      rw [← regionVals_map_fst σ env]; exact List.mem_map_of_mem hpv
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem
      (fun hj hk hne => disjoint8_words _ (List.mem_range.1 hj) (List.mem_range.1 hk)
        (hn _ hpv') hne) List.nodup_range
  · grind

/-- **The encoded entry state satisfies the entry conditions of the layout**, from a base state
    that satisfies them, when the parameter registers are distinct and none is `%rsp`, every
    parameter is carried in a register, and every bounded register is within its bound in the
    encoded register file. -/
theorem regions_encodeEntry {σ : AbiLayout} {s0 : AState} (env : Env)
    (hreg : (σ.args.map (·.reg)).Nodup) (hrsp : ∀ a ∈ σ.args, a.reg ≠ "%rsp")
    (hrc : σ.RegCarried) (hs0 : σ.Regions s0)
    (hb : ∀ b ∈ σ.bounds, (σ.entryRegs s0 env b.1).toNat ≤ b.2) :
    σ.Regions (σ.encodeEntry s0 env) := by
  have hsp : σ.entryRegs s0 env "%rsp" = s0.regs "%rsp" :=
    entryRegs_of_not_scalar s0 env fun a ha h => absurd h (hrsp a ha)
  refine ⟨hb, fun i j p q hij hpi hqj k k' hk hk' => ?_,
    fun p hp k hk o ho1 ho2 => ?_, stackIn_of_regCarried hrc _⟩
  · simp only [encodeEntry, entryRegs_region s0 env hreg (List.mem_of_getElem? hpi),
      entryRegs_region s0 env hreg (List.mem_of_getElem? hqj)]
    exact hs0.2.1 i j p q hij hpi hqj k k' hk hk'
  · simp only [encodeEntry, hsp, entryRegs_region s0 env hreg hp]
    exact hs0.2.2.1 p hp k hk o ho1 ho2

/-- **The layout reads the environment off the encoded entry state**, when every parameter
    value fits its kind, the constants are bound to their values, no other name is bound, the
    parameter registers are distinct, and no region of `s0` wraps around the address space. -/
theorem envOf_encodeEntry {σ : AbiLayout} {s0 : AState} {env : Env}
    (hreg : (σ.args.map (·.reg)).Nodup) (hs0 : σ.Regions s0)
    (hn : ∀ p ∈ σ.regions, 8 * p.2 ≤ 2 ^ 64)
    (hfit : ∀ a ∈ σ.args, ∃ v, env a.name = some v ∧ a.Fits v)
    (hc : ∀ c ∈ σ.consts, env c.1 = some c.2) (hdom : ∀ y, (env y).isSome → y ∈ σ.envNames) :
    σ.EnvOf (σ.encodeEntry s0 env) env := by
  refine ⟨fun a ha => ?_, hc, hdom⟩
  obtain ⟨v, hv, hf⟩ := hfit a ha
  rw [hv]
  congr 1
  unfold AbiArg.Fits at hf
  unfold AbiArg.read
  split at hf
  · rename_i hk
    rw [hk]
    simp only [encodeEntry, entryRegs_scalar s0 env hreg ha hk, hv, Option.getD_some]
    exact hf
  · rename_i n hk
    rw [hk]
    have hR : (a.reg, n) ∈ σ.regions := List.mem_filterMap.2 ⟨a, ha, by simp [AbiArg.region, hk]⟩
    have hw : ∀ j, j < n → read64 (writeWords s0.mem (σ.entryWrites s0 env))
        (s0.regs a.reg + BitVec.ofNat 64 (8 * j)) = valWordAt v j := fun j hj =>
      read64_writeWords_mem _ _ (entryWrites_pairwise env hs0 hn)
        (List.mem_flatMap.2 ⟨((a.reg, n), v),
          List.mem_filterMap.2 ⟨a, ha, by simp [AbiArg.region, hk, hv]⟩,
          List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩⟩)
    simp only [encodeEntry, entryRegs_region s0 env hreg hR, wordsAt]
    rw [hf]
    congr 1
    exact List.map_congr_left fun j hj => by rw [hw j (List.mem_range.1 hj)]

end AbiLayout

/-! ## Decoding the read-back -/

open Classical in
/-- The value of `β` whose encoding is `v`, when there is one. -/
noncomputable def decodeEnc (β : Type) [HaxEnc β] (v : Value) : Option β :=
  if h : ∃ y : β, HaxEnc.enc y = v then some h.choose else none

/-- Under an injective encoding, an encoding decodes to its value. -/
theorem decodeEnc_enc {β : Type} [HaxEnc β] [HaxEnc.Inj β] (y : β) :
    decodeEnc β (HaxEnc.enc y) = some y := by
  unfold decodeEnc
  split
  · rename_i h
    exact congrArg some (HaxEnc.Inj.inj h.choose_spec)
  · rename_i h
    exact absurd ⟨y, rfl⟩ h

/-- **Decoding the read-back.** When `σ` reads back the encoding of `y` from the entry state
    `sa` and the exit state `sa'`, the read-back value decodes to `y`. -/
theorem decodeEnc_resultOf {β : Type} [HaxEnc β] [HaxEnc.Inj β] {σ : AbiLayout}
    {sa sa' : AState} {y : β} (h : σ.ResultOf sa sa' (HaxEnc.enc y)) :
    decodeEnc β (σ.result.read sa sa') = some y := by
  rw [← show HaxEnc.enc y = σ.result.read sa sa' from h]
  exact decodeEnc_enc y

end CatCrypt.Crypto.SecureCompilation.Haxc
