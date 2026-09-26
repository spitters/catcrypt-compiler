/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

/-!
# The multi-limb conditional-subtract round over `JInstr 64`

`condSubRoundN res q sav rtop` is the branch-free conditional subtract of an
`n`-limb modulus held in registers `q` from an `(n+1)`-word value held in the
result registers `res` and the top word `rtop`:

* `SUB res₀, q₀` followed by the `SBB` chain `emitSbbChain` over the remaining
  limbs, and `SBB rtop, 0`, so that `CF` is the final borrow of the
  `(n+1)`-word trial subtraction;
* `CMOVB resᵢ, savᵢ` for every limb, restoring the saved copy `sav` when the trial
  borrowed.

`condSubRoundFullN` appends the bookkeeping for the next round (`sav ← res`,
`rtop ← 0`).

The limb count and the register names are parameters; the modulus enters only
through the registers `q`. The register-allocated rounds of
`Curve4MontMulProvenEmit`, `Curve6MontMulProvenEmit`, `Fe25519MulProvenEmit` and
`Sm2MontMulProvenEmit` are instances.

## Main results

* `condSubRoundN_regs`: over `runBlock`, the result registers hold the saved copy
  when `V < P` and the ripple difference `subLimbs` otherwise, where `V` is the
  `(n+1)`-word input value and `P` the modulus value.
* `condSubRoundN_val`: the value form, `valLimbs res = (V − P) mod 2^(64n)` when
  `P ≤ V`, and `valLimbs sav` otherwise.
* `condSubRoundN_val_lt_two`: under `V < 2P`, `valLimbs res = V − P` or `valLimbs sav`.
* `condSubRoundN_pres`: registers outside `res` and `rtop` are preserved.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.CondSubRoundGeneric

open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.X86Backend.Cios4LimbProven
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldAddSubTierA
open CatCrypt.Crypto.SecureCompilation.X86Backend.FieldSubRunBlock

/-! ## 1. The blocks -/

/-- `CMOVB dᵢ, vᵢ` over parallel register lists. -/
def cmovbChain : List String → List String → List (JInstr 64)
  | [], _ => []
  | _, [] => []
  | d :: ds, v :: vs => .cmovb d (.reg v) :: cmovbChain ds vs

/-- `MOV dᵢ, vᵢ` over parallel register lists. -/
def movChain : List String → List String → List (JInstr 64)
  | [], _ => []
  | _, [] => []
  | d :: ds, v :: vs => .mov d (.reg v) :: movChain ds vs

/-- One branch-free conditional-subtract round: trial-subtract the limbs `q` from
    `res` through the borrow chain and the top word `rtop`, then `CMOVB` each
    `resᵢ` back to `savᵢ` on a final borrow. -/
def condSubRoundN : List String → List String → List String → String → List (JInstr 64)
  | r :: rs, p :: ps, sav, rtop =>
      (JInstr.sub r (.reg p) :: emitSbbChain rs ps)
        ++ (JInstr.sbb rtop (.imm 0) :: cmovbChain (r :: rs) sav)
  | _, _, _, _ => []

/-- One conditional-subtract round followed by the bookkeeping for the next round:
    `sav ← res`, `rtop ← 0`. -/
def condSubRoundFullN (res q sav : List String) (rtop : String) : List (JInstr 64) :=
  condSubRoundN res q sav rtop ++ movChain sav res ++ [JInstr.xor_ rtop (.reg rtop)]

/-! ## 2. Single-instruction bridges -/

/-- `SBB dst, n` writes `subBorrowWord dst n CF` into `dst`. -/
theorem emit_sbb_imm_word (s : JState 64) (dst : String) (n : Nat) :
    (evalInstr s (.sbb dst (.imm n))).get dst
      = subBorrowWord (s.get dst) (BitVec.ofNat 64 n)
          (BitVec.ofNat 1 (if s.flagB (·.cf) then 1 else 0)) := by
  rw [subBorrowWord_eq_sub_borrow]
  simp only [evalInstr, JState.get, JState.writeB5W, x86_SBB, JOperand.eval]
  rcases h : s.flagB (·.cf) with _ | _ <;> simp

/-- `SBB dst, n` sets `CF` to the borrow-out `dst < n + CF`. -/
theorem emit_sbb_imm_cf (s : JState 64) (dst : String) (n : Nat) :
    (evalInstr s (.sbb dst (.imm n))).flagB (·.cf)
      = decide ((s.get dst).toNat < (BitVec.ofNat 64 n).toNat
          + (if s.flagB (·.cf) then 1 else 0)) := by
  have hd := (s.get dst).isLt
  have hsrc := (BitVec.ofNat 64 n).isLt
  simp only [evalInstr, JState.flagB, JState.writeB5W, x86_SBB, sub_borrow,
    JOperand.eval, wunsigned, Option.getD_some]
  refine decide_eq_decide.mpr ?_
  by_cases hc : (Option.getD s.flags.cf false : Bool) = true
  · simp only [hc, ↓reduceIte, Nat.cast_one, ne_eq]
    rw [show ((s.get dst).toNat : Int) - ↑(BitVec.ofNat 64 n).toNat - 1
          = ((s.get dst).toNat : Int) - (↑(BitVec.ofNat 64 n).toNat + 1) by ring,
      ofInt_toNat_borrow _ (by push_cast; omega) (by push_cast; omega)]
    omega
  · simp only [hc, ↓reduceIte, Bool.false_eq_true, Nat.cast_zero, sub_zero, Nat.add_zero, ne_eq]
    rw [show ((s.get dst).toNat : Int) - ↑(BitVec.ofNat 64 n).toNat
          = ((s.get dst).toNat : Int) - (↑(BitVec.ofNat 64 n).toNat + 0) by ring,
      ofInt_toNat_borrow _ (by push_cast; omega) (by push_cast; omega)]
    omega

/-- `SBB dst, n` writes only `dst`. -/
theorem emit_sbb_imm_other (s : JState 64) (dst r : String) (n : Nat) (hr : r ≠ dst) :
    (evalInstr s (.sbb dst (.imm n))).get r = s.get r := by
  simp only [evalInstr, JState.get, JState.writeB5W, if_neg hr]

/-- `CMOVB dst, src` writes `src` into `dst` when `CF` is set and preserves every
    other register. -/
theorem emit_cmovb_get (s : JState 64) (dst src r : String) :
    (evalInstr s (.cmovb dst (.reg src))).get r
      = if r = dst then (if s.flagB (·.cf) then s.get src else s.get dst) else s.get r := by
  simp only [evalInstr, x86_CMOVcc, JState.setReg, JState.get, JOperand.eval]

/-- `CMOVB` leaves `CF` unchanged. -/
theorem emit_cmovb_cf (s : JState 64) (dst src : String) :
    (evalInstr s (.cmovb dst (.reg src))).flagB (·.cf) = s.flagB (·.cf) := by
  simp [evalInstr, x86_CMOVcc, JState.setReg, JState.flagB]

/-! ## 3. The `CMOVB` chain -/

/-- `runBlock` distributes over `++`. -/
private theorem runBlock_append (s : JState 64) (xs ys : List (JInstr 64)) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => exact ih (evalInstr s i)

/-- The `CMOVB` chain leaves `CF` unchanged. -/
theorem cmovbChain_cf :
    ∀ (ds vs : List String) (s : JState 64),
      (runBlock s (cmovbChain ds vs)).flagB (·.cf) = s.flagB (·.cf)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, v :: vs, s => by
      rw [cmovbChain, runBlock_cons, cmovbChain_cf ds vs, emit_cmovb_cf]

/-- The `CMOVB` chain writes only `ds`. -/
theorem cmovbChain_other :
    ∀ (ds vs : List String) (s : JState 64) (r : String), r ∉ ds →
      (runBlock s (cmovbChain ds vs)).get r = s.get r
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, _, _ => rfl
  | d :: ds, v :: vs, s, r, hr => by
      rw [cmovbChain, runBlock_cons, cmovbChain_other ds vs _ r
        (fun h => hr (List.mem_cons_of_mem _ h)), emit_cmovb_get,
        if_neg (fun h => hr (by subst h; exact List.mem_cons_self))]

/-- **The `CMOVB` chain selects.** With `ds` duplicate-free and disjoint from `vs`
    (equal lengths), the destinations hold `vs` when `CF` is set and keep their
    values otherwise. -/
theorem cmovbChain_regs :
    ∀ (ds vs : List String) (s : JState 64), ds.length = vs.length → ds.Nodup →
      (∀ d ∈ ds, ∀ v ∈ vs, d ≠ v) →
      ds.map (runBlock s (cmovbChain ds vs)).get
        = if s.flagB (·.cf) then vs.map s.get else ds.map s.get
  | [], [], s, _, _, _ => by simp [cmovbChain]
  | [], _ :: _, _, h, _, _ => by simp at h
  | _ :: _, [], _, h, _, _ => by simp at h
  | d :: ds, v :: vs, s, hlen, hnd, hdisj => by
      have hnd' := List.nodup_cons.mp hnd
      set s1 := evalInstr s (.cmovb d (.reg v)) with hs1
      have hcf1 : s1.flagB (·.cf) = s.flagB (·.cf) := emit_cmovb_cf s d v
      have htail := cmovbChain_regs ds vs s1 (by simpa using hlen) hnd'.2
        (fun a ha b hb => hdisj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      have hd : (runBlock s1 (cmovbChain ds vs)).get d = s1.get d :=
        cmovbChain_other ds vs s1 d hnd'.1
      have hs1d : s1.get d = if s.flagB (·.cf) then s.get v else s.get d := by
        rw [hs1, emit_cmovb_get, if_pos rfl]
      have hvs : vs.map s1.get = vs.map s.get := by
        apply List.map_congr_left; intro r hr
        rw [hs1, emit_cmovb_get, if_neg (fun h => hdisj d List.mem_cons_self r
          (List.mem_cons_of_mem _ hr) h.symm)]
      have hds : ds.map s1.get = ds.map s.get := by
        apply List.map_congr_left; intro r hr
        rw [hs1, emit_cmovb_get, if_neg (fun h => hnd'.1 (by subst h; exact hr))]
      rw [cmovbChain, runBlock_cons, List.map_cons, hd, htail, hcf1, hvs, hds, hs1d]
      split <;> simp

/-! ## 4. The round over `runBlock` -/

/-- **The round, register form.** With `res` duplicate-free and disjoint from the
    modulus registers `q` and from the saved copy `sav` (all of one length `n ≥ 1`),
    and `rtop` outside all three: after the round the result registers hold `sav`
    when the `(n+1)`-word value `V = valLimbs res + 2^(64n)·rtop` is below
    `P = valLimbs q`, and the ripple difference `subLimbs res q 0` otherwise. -/
theorem condSubRoundN_regs (res q sav : List String) (rtop : String) (s : JState 64)
    (hne : res ≠ []) (hq : q.length = res.length) (hsav : sav.length = res.length)
    (hfresh : ChainFresh res q) (hresSav : ∀ r ∈ res, ∀ v ∈ sav, r ≠ v)
    (hrtopRes : rtop ∉ res) (hrtopSav : rtop ∉ sav) :
    res.map (runBlock s (condSubRoundN res q sav rtop)).get
      = if valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
            < valLimbs (q.map s.get)
        then sav.map s.get
        else (subLimbs (res.map s.get) (q.map s.get) 0).1 := by
  obtain ⟨r, rs, rfl⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨p, ps, rfl⟩ : ∃ p ps, q = p :: ps := by
    cases q with
    | nil => simp at hq
    | cons p ps => exact ⟨p, ps, rfl⟩
  have hnd := List.nodup_cons.mp hfresh.ds_nodup
  have hrp : r ≠ p := hfresh.ds_ss r List.mem_cons_self p List.mem_cons_self
  rw [condSubRoundN, runBlock_append, runBlock_cons]
  set s1 := evalInstr s (.sub r (.reg p)) with hs1
  set s2 := runBlock s1 (emitSbbChain rs ps) with hs2
  set s3 := evalInstr s2 (.sbb rtop (.imm 0)) with hs3
  -- the leading `SUB`
  have hs1r : s1.get r = subBorrowWord (s.get r) (s.get p) 0 := by
    rw [hs1, emit_sub_word]; simp [subBorrowWord]
  have hs1cf : (s1.flagB (·.cf) = true)
      = (borrowOutBit (s.get r) (s.get p) 0 = 1) := by
    rw [hs1, emit_sub_cf]
    simp only [borrowOutBit, decide_eq_true_eq]
    have : ((0 : BitVec 1)).toNat = 0 := rfl
    rw [this, Nat.add_zero]
    split <;> simp_all
  have hs1rs : rs.map s1.get = rs.map s.get := by
    apply List.map_congr_left; intro x hx
    rw [hs1]; exact emit_sub_other s r p x (fun h => hnd.1 (h ▸ hx))
  have hs1ps : ps.map s1.get = ps.map s.get := by
    apply List.map_congr_left; intro x hx
    rw [hs1]; exact emit_sub_other s r p x
      (fun h => hfresh.ds_ss r List.mem_cons_self x (List.mem_cons_of_mem _ hx) h.symm)
  -- the `SBB` chain
  have hfresh' : ChainFresh rs ps :=
    { ds_nodup := hnd.2
      ds_ss := fun a ha b hb => hfresh.ds_ss a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb) }
  obtain ⟨hchain, hchaincf⟩ := emitSbbChain_runBlock rs ps (rs.map s.get) (ps.map s.get)
    (borrowOutBit (s.get r) (s.get p) 0) s1 (by simp) (by simp)
    (by simpa using hq.symm) hfresh' hs1rs hs1ps hs1cf
  have hs2r : s2.get r = s1.get r :=
    emitSbbChain_preserves rs ps r s1 (fun x hx h => hnd.1 (h ▸ hx))
  have hs2top : s2.get rtop = s.get rtop := by
    rw [hs2, emitSbbChain_preserves rs ps rtop s1
      (fun x hx h => hrtopRes (h ▸ List.mem_cons_of_mem _ hx)), hs1]
    exact emit_sub_other s r p rtop (fun h => hrtopRes (h ▸ List.mem_cons_self))
  have hdiff : (r :: rs).map s2.get = (subLimbs ((r :: rs).map s.get) ((p :: ps).map s.get) 0).1 := by
    simp only [List.map_cons, subLimbs, List.headD_cons, List.tail_cons]
    rw [hs2r, hs1r]
    exact congrArg _ hchain
  -- the save registers are untouched before the `CMOVB` chain
  have hsav3 : sav.map s3.get = sav.map s.get := by
    apply List.map_congr_left; intro v hv
    have hvr : v ≠ r := fun h => hresSav r List.mem_cons_self v hv h.symm
    have hvrs : ∀ x ∈ rs, v ≠ x := fun x hx h =>
      hresSav x (List.mem_cons_of_mem _ hx) v hv h.symm
    rw [hs3, emit_sbb_imm_other s2 rtop v 0 (fun h => hrtopSav (h ▸ hv)), hs2,
      emitSbbChain_preserves rs ps v s1 hvrs, hs1]
    exact emit_sub_other s r p v hvr
  have hres3 : (r :: rs).map s3.get = (r :: rs).map s2.get := by
    apply List.map_congr_left; intro x hx
    rw [hs3]; exact emit_sbb_imm_other s2 rtop x 0 (fun h => hrtopRes (h ▸ hx))
  -- the final borrow
  set b1 := (subLimbs (rs.map s.get) (ps.map s.get) (borrowOutBit (s.get r) (s.get p) 0)).2
    with hb1
  have hbit := bit_toNat b1
  have hs3cf : s3.flagB (·.cf) = decide ((s.get rtop).toNat < b1.toNat) := by
    rw [hs3, emit_sbb_imm_cf, hs2top]
    have h0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
    rw [h0, Nat.zero_add, hbit]
    congr 2
    rcases hc : s2.flagB (·.cf) with _ | _ <;> simp_all
  -- reconstruction of the ripple difference
  set U := (r :: rs).map s.get with hU
  set Q := (p :: ps).map s.get with hQ
  have hrecon := subLimbs_reconstruct U Q 0
  have hUlen : U.length = (r :: rs).length := by simp [hU]
  have hQtake : Q.take U.length = Q := by
    rw [List.take_of_length_le]; simp only [hU, hQ, List.length_map]; omega
  have hb1eq : (subLimbs U Q 0).2 = b1 := by
    simp only [hU, hQ, List.map_cons, subLimbs, List.headD_cons, List.tail_cons, hb1]
  rw [hQtake, hb1eq, hUlen] at hrecon
  have hDlt := valLimbs_lt_pow (subLimbs U Q 0).1
  rw [subLimbs_length, hUlen] at hDlt
  have hb1le : b1.toNat ≤ 1 := by have := b1.isLt; omega
  have h0 : ((0 : BitVec 1)).toNat = 0 := rfl
  rw [h0, Nat.add_zero] at hrecon
  -- the `CMOVB` chain
  rw [runBlock_cons, ← hs3, cmovbChain_regs (r :: rs) sav s3 (by simp [hsav]) hfresh.ds_nodup
    hresSav, hsav3, hres3, hdiff, hs3cf]
  set N := (2 ^ 64) ^ (r :: rs).length with hN
  set T := (s.get rtop).toNat with hT
  set D := valLimbs (subLimbs U Q 0).1 with hD
  have hiff : T < b1.toNat ↔ valLimbs U + N * T < valLimbs Q := by
    rcases (show b1.toNat = 0 ∨ b1.toNat = 1 by omega) with hb | hb
    · rw [hb, Nat.mul_zero] at hrecon
      rw [hb]
      constructor
      · intro h; omega
      · intro h; omega
    · rw [hb, Nat.mul_one] at hrecon
      rw [hb]
      constructor
      · intro h
        have hT0 : T = 0 := by omega
        rw [hT0, Nat.mul_zero]; omega
      · intro h
        by_contra hc
        have hT1 : 0 < T := by omega
        have := Nat.le_mul_of_pos_right N hT1
        omega
  simp only [decide_eq_true_eq]
  exact if_congr hiff rfl rfl

/-- The ripple difference at borrow-in `0` of an `n`-limb value `U` (with top word
    `T`) and an `n`-limb value `Q`, when `Q ≤ U + 2^(64n)·T`, is
    `(U + 2^(64n)·T − Q) mod 2^(64n)`. -/
theorem subLimbs_val_of_le (U Q : List (BitVec 64)) (T : Nat) (hlen : Q.length = U.length)
    (hle : ¬ valLimbs U + (2 ^ 64) ^ U.length * T < valLimbs Q) :
    valLimbs (subLimbs U Q 0).1
      = (valLimbs U + (2 ^ 64) ^ U.length * T - valLimbs Q) % (2 ^ 64) ^ U.length := by
  have hrecon := subLimbs_reconstruct U Q 0
  rw [List.take_of_length_le (by omega)] at hrecon
  have hDlt := valLimbs_lt_pow (subLimbs U Q 0).1
  rw [subLimbs_length] at hDlt
  have h0 : ((0 : BitVec 1)).toNat = 0 := rfl
  rw [h0, Nat.add_zero] at hrecon
  set N := (2 ^ 64) ^ U.length with hN
  set D := valLimbs (subLimbs U Q 0).1 with hD
  have hb1le : (subLimbs U Q 0).2.toNat ≤ 1 := by have := (subLimbs U Q 0).2.isLt; omega
  rcases (show (subLimbs U Q 0).2.toNat = 0 ∨ (subLimbs U Q 0).2.toNat = 1 by omega) with hb | hb
  · rw [hb, Nat.mul_zero] at hrecon
    rw [show valLimbs U + N * T - valLimbs Q = D + N * T by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hDlt]
  · rw [hb, Nat.mul_one] at hrecon
    have hT1 : 0 < T := by
      by_contra hc
      have hT0 : T = 0 := by omega
      rw [hT0, Nat.mul_zero] at hle
      omega
    obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [show valLimbs U + N * (T' + 1) - valLimbs Q = D + N * T' by rw [Nat.mul_succ]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hDlt]

/-- **The round, value form.** Under the hypotheses of `condSubRoundN_regs`, with
    `V = valLimbs res + 2^(64n)·rtop` and `P = valLimbs q`: the result registers hold
    `valLimbs sav` when `V < P` and `(V − P) mod 2^(64n)` otherwise. -/
theorem condSubRoundN_val (res q sav : List String) (rtop : String) (s : JState 64)
    (hne : res ≠ []) (hq : q.length = res.length) (hsav : sav.length = res.length)
    (hfresh : ChainFresh res q) (hresSav : ∀ r ∈ res, ∀ v ∈ sav, r ≠ v)
    (hrtopRes : rtop ∉ res) (hrtopSav : rtop ∉ sav) :
    valLimbs (res.map (runBlock s (condSubRoundN res q sav rtop)).get)
      = if valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
            < valLimbs (q.map s.get)
        then valLimbs (sav.map s.get)
        else (valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
            - valLimbs (q.map s.get)) % (2 ^ 64) ^ res.length := by
  rw [condSubRoundN_regs res q sav rtop s hne hq hsav hfresh hresSav hrtopRes hrtopSav]
  split
  · rfl
  · rename_i hle
    have h := subLimbs_val_of_le (res.map s.get) (q.map s.get) (s.get rtop).toNat
      (by simp [hq]) (by simpa using hle)
    simpa using h

/-- **The round below `2P`.** When additionally `V < 2P`, the result registers hold
    `V − P` when `P ≤ V` and `valLimbs sav` otherwise. -/
theorem condSubRoundN_val_lt_two (res q sav : List String) (rtop : String) (s : JState 64)
    (hne : res ≠ []) (hq : q.length = res.length) (hsav : sav.length = res.length)
    (hfresh : ChainFresh res q) (hresSav : ∀ r ∈ res, ∀ v ∈ sav, r ≠ v)
    (hrtopRes : rtop ∉ res) (hrtopSav : rtop ∉ sav)
    (hv : valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
      < 2 * valLimbs (q.map s.get)) :
    valLimbs (res.map (runBlock s (condSubRoundN res q sav rtop)).get)
      = if valLimbs (q.map s.get)
            ≤ valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
        then valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
            - valLimbs (q.map s.get)
        else valLimbs (sav.map s.get) := by
  rw [condSubRoundN_val res q sav rtop s hne hq hsav hfresh hresSav hrtopRes hrtopSav]
  have hP := valLimbs_lt_pow (q.map s.get)
  rw [List.length_map, hq] at hP
  by_cases hlt : valLimbs (res.map s.get) + (2 ^ 64) ^ res.length * (s.get rtop).toNat
      < valLimbs (q.map s.get)
  · rw [if_pos hlt, if_neg (by omega)]
  · rw [if_neg hlt, if_pos (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The round writes only `res` and `rtop`. -/
theorem condSubRoundN_pres (res q sav : List String) (rtop : String) (s : JState 64)
    (x : String) (hxRes : x ∉ res) (hxTop : x ≠ rtop) :
    (runBlock s (condSubRoundN res q sav rtop)).get x = s.get x := by
  match res, q with
  | [], _ => rfl
  | _ :: _, [] => rfl
  | r :: rs, p :: ps =>
      rw [condSubRoundN, runBlock_append, runBlock_cons, runBlock_cons,
        cmovbChain_other _ _ _ x hxRes, emit_sbb_imm_other _ rtop x 0 hxTop,
        emitSbbChain_preserves rs ps x _ (fun y hy h => hxRes (h ▸ List.mem_cons_of_mem _ hy)),
        emit_sub_other s r p x (fun h => hxRes (h ▸ List.mem_cons_self))]

end CatCrypt.Crypto.SecureCompilation.X86Backend.CondSubRoundGeneric
