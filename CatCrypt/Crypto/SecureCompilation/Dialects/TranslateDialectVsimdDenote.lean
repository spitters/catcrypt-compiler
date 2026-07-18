/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd

set_option autoImplicit false

/-!
# Front-general `vsimd` preservation (universal `denote = spec`)

`TranslateDialectVsimd` pins the front-generated `vsimd` kernels per-input with
`native_decide` (the concrete pilots). This module proves the **front-general**
statement: for *any* covered `vsimd` `LowCT` body, the `Com catCryptDialect`
prefix `translateDialectControlV` emits denotes exactly the body's `SimdOp`-fold
semantics, for *all* 128-bit inputs — a symbolic induction over the coverage
derivation, with the per-op step discharged by the fact that the emitted
`CatCryptDialect` op (`.vsimd op` / `.vpsrldqC n` / `.vpslldqC n`) denotes by the
*same waist* (`SimdOp.denote` / `· >>> n*8` / `· <<< n*8`) as the pure semantics.

Composing with the verified `cryptoDialectToJasminCom` lowering preservation, any
`vsimd` kernel gets a universal `denote = spec` — no render-equality-to-a-twin.
-/

namespace CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd

open CatCrypt.Crypto.SecureCompilation.CryptoSSA
open CatCrypt.Crypto.SecureCompilation.LowCTToCryptoSSA
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect (SimdOp)
open CatCrypt.Crypto.SecureCompilation.VIR.DialectVarBridge
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirect
open CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectDirectControl
open CatCrypt.Crypto.Jasmin.LowCT (LowCT Located)

/-! ## 1. Partial `SEnv` semantics of a covered `vsimd` body -/

/-- A per-name partial environment of 128-bit vector values (`none` = unbound). -/
abbrev SEnv := String → Option (BitVec 128)

/-- Update a name in an `SEnv`. -/
def SEnv.upd (env : SEnv) (name : String) (val : BitVec 128) : SEnv :=
  fun s => if s = name then some val else env s

/-- The pure semantics of a covered `vsimd` body as a partial `SEnv` transformer:
    each op reads its 128-bit operands from `env` and binds its destination to the
    matching `SimdOp`/byte-shift value — the SAME waist the front's emitted
    `CatCryptDialect` op denotes by (`SimdOp.denote op`, `· >>> n*8`, `· <<< n*8`,
    or the baked constant `val` for `vconst`). `none` when an operand is unbound or
    the shape is not a covered `vsimd` op. -/
def semV : LowCT → SEnv → Option SEnv
  | .RSkip, env => some env
  | .RBlock body, env => semV body env
  | .RSeq c₁ c₂, env => (semV c₁ env).bind (fun e => semV c₂ e)
  | .RCall fname dst args, env =>
      match vsimdTag fname, args with
      | some (.binary op), [a, b] =>
          match env a.locVar, env b.locVar with
          | some av, some bv => some (env.upd dst.locVar (SimdOp.denote op av bv))
          | _, _ => none
      | some (.srl n), [a] =>
          match env a.locVar with
          | some av => some (env.upd dst.locVar (av >>> (n * 8)))
          | _ => none
      | some (.sll n), [a] =>
          match env a.locVar with
          | some av => some (env.upd dst.locVar (av <<< (n * 8)))
          | _ => none
      | some (.ushuf imm), [a] =>
          match env a.locVar with
          | some av => some (env.upd dst.locVar (SimdOp.denote (.vpshufd imm) av av))
          | _ => none
      | some (.ukeygen rcon), [a] =>
          match env a.locVar with
          | some av => some (env.upd dst.locVar (SimdOp.denote (.vaeskeygen rcon) av av))
          | _ => none
      | some (.vconst val), [] => some (env.upd dst.locVar val)
      | some .sha256rnds2, [a, b, c] =>
          match env a.locVar, env b.locVar, env c.locVar with
          | some av, some bv, some cv =>
              some (env.upd dst.locVar (vsha256rnds2W av bv cv))
          | _, _, _ => none
      | some .sha256msg1, [a, b] =>
          match env a.locVar, env b.locVar with
          | some av, some bv => some (env.upd dst.locVar (vsha256msg1W av bv))
          | _, _ => none
      | some .sha256msg2, [a, b] =>
          match env a.locVar, env b.locVar with
          | some av, some bv => some (env.upd dst.locVar (vsha256msg2W av bv))
          | _, _ => none
      | _, _ => none
  | _, _ => none

/-- Consistency between a `VarMap` at `Γ`, a `Γ`-valuation `V`, and an `SEnv`:
    every name's `SEnv` value is exactly the 128-bit slot it resolves to in `V`
    (or `none` if the name is not a `.sword 128` slot in the `VarMap`). -/
def ConsistentV {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnv) : Prop :=
  ∀ s : String, (lookupReg128 vm s).map (fun v => (toVIRVar v).lookup V) = env s

/-! ## 2. `lookupReg128`/`VarMap.bind` interaction -/

/-- `lookupReg128` after a `.sword 128` `bind`: the bound name resolves to `.here`,
    every other name to the `.there`-shift of its prior resolution. -/
theorem lookupReg128_bind {Γ : Ctx} (vm : VarMap Γ) (name s : String) :
    lookupReg128 (vm.bind (t := .sword 128) name) s
      = if s = name then some .here else (lookupReg128 vm s).map .there := by
  by_cases hs : s = name
  · subst hs; simp [lookupReg128, VarMap.bind]
  · simp only [lookupReg128, VarMap.bind, if_neg hs]
    cases hl : vm.lookup s with
    | none => rfl
    | some p =>
        obtain ⟨t', v⟩ := p
        cases t' with
        | bit => rfl
        | unit => rfl
        | pair a b => rfl
        | sum a b => rfl
        | memref n => rfl
        | sword n =>
            by_cases hn : n = 128
            · subst hn; rfl
            · split <;> simp_all

/-! ## 3. The single-op step (shared across all `vsimd` arms) -/

/-- One `vsimd` op step: emitting a `.sword 128` `varBind` of an expression `e`
    over the entry valuation `V` extends consistency by binding `dst` to `e.denote V`,
    and the emitted prefix, applied to any tail, denotes that tail at the extended
    valuation. This is the common core of all five `vsimd` front arms (binary op,
    `vpsrldq`/`vpslldq` shift, `vpshufd`, `vaeskeygen`) — they differ only in `e`. -/
theorem vsimd_step {Γ : Ctx} (vm : VarMap Γ)
    (V : Ctxt.Valuation (d := catCryptDialect) Γ) (env : SEnv)
    (hc : ConsistentV vm V env) (dst : String)
    (e : Expr catCryptDialect Γ (.sword 128)) :
    ConsistentV (vm.bind dst) (V.extend (e.denote V)) (env.upd dst (e.denote V)) ∧
    ∀ {t : CryptoTy} (tail : Com catCryptDialect (.sword 128 :: Γ) t),
      ∃ com, (ComCont.varBind e) tail = some com ∧
        com.denote V = tail.denote (V.extend (e.denote V)) := by
  refine ⟨?_, ?_⟩
  · intro s
    rw [lookupReg128_bind]
    by_cases hsd : s = dst
    · subst hsd
      simp only [if_pos rfl, Option.map_some, SEnv.upd, if_pos rfl]
      rfl
    · simp only [if_neg hsd, SEnv.upd, if_neg hsd, Option.map_map]
      rw [← hc s]
      apply Option.map_congr
      intro v _
      rfl
  · intro t tail
    exact ⟨Com.var e tail, rfl, rfl⟩

/-! ## 4. Front-general preservation -/

/-- **Front-general `vsimd` preservation.** For any covered `vsimd` body `c`, the
    `Com`-prefix `o.cont` the front `translateDialectControlV` emits denotes exactly
    the body's `semV` `SimdOp`-fold semantics: there is an extended valuation `V'`,
    consistent with the final `VarMap` and the `semV`-updated `SEnv`, on which every
    tail's denotation through `o.cont` (at the entry valuation `V`) equals the tail's
    denotation at `V'`. Proved by induction on the coverage derivation. -/
theorem translateDialectControlV_denote {c : LowCT} (hcov : IsCoveredV c) :
    ∀ {Γ : Ctx} (vm : VarMap Γ) (V : Ctxt.Valuation (d := catCryptDialect) Γ)
      (env env' : SEnv) (o : DTransOut Γ),
      ConsistentV vm V env →
      translateDialectControlV vm c = some o →
      semV c env = some env' →
      ∃ V' : Ctxt.Valuation (d := catCryptDialect) o.Γ',
        ConsistentV o.vm V' env' ∧
        ∀ {t : CryptoTy} (tail : Com catCryptDialect o.Γ' t),
          ∃ com, o.cont tail = some com ∧ com.denote V = tail.denote V' := by
  induction hcov with
  | rSkip =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectControlV] at htr
      simp only [semV, Option.some.injEq] at hsem
      obtain rfl := Option.some.inj htr
      subst hsem
      exact ⟨V, hc, fun tail => ⟨tail, rfl, rfl⟩⟩
  | @rBlock body hbody ih =>
      intro Γ vm V env env' o hc htr hsem
      simp only [translateDialectControlV] at htr
      simp only [semV] at hsem
      exact ih vm V env env' o hc htr hsem
  | @rSeq c₁ c₂ h₁ h₂ ih₁ ih₂ =>
      intro Γ vm V env env' o hc htr hsem
      rcases ht1 : translateDialectControlV vm c₁ with _ | o₁
      · simp [translateDialectControlV, ht1] at htr
      · rcases ht2 : translateDialectControlV o₁.vm c₂ with _ | o₂
        · simp [translateDialectControlV, ht1, ht2] at htr
        · rcases hs1 : semV c₁ env with _ | env₁
          · simp [semV, hs1] at hsem
          · simp only [semV, hs1, Option.bind_some] at hsem
            simp only [translateDialectControlV, ht1, ht2, Option.some.injEq] at htr
            obtain rfl := htr
            obtain ⟨V₁, hc₁, hcont₁⟩ := ih₁ vm V env env₁ o₁ hc ht1 hs1
            obtain ⟨V₂, hc₂, hcont₂⟩ := ih₂ o₁.vm V₁ env₁ env' o₂ hc₁ ht2 hsem
            refine ⟨V₂, hc₂, ?_⟩
            intro t tail
            obtain ⟨com₂, hcom₂, hden₂⟩ := hcont₂ tail
            obtain ⟨com, hcom, hden⟩ := hcont₁ com₂
            refine ⟨com, ?_, ?_⟩
            · show ComCont.comp o₁.cont o₂.cont tail = some com
              simp only [ComCont.comp, hcom₂, hcom]
            · rw [hden, hden₂]
  | rVsimd fname dst args htag =>
      intro Γ vm V env env' o hc htr hsem
      obtain ⟨tg, htg⟩ := Option.isSome_iff_exists.mp htag
      cases tg with
      | binary op =>
          rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨cc, rest⟩⟩⟩
          · simp [semV, htg] at hsem
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · rcases hlb : lookupReg128 vm b.locVar with _ | vb
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = none := by rw [← hc b.locVar, hlb]; rfl
                simp [hae, hbe] at hsem
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = some ((toVIRVar vb).lookup V) := by
                  rw [← hc b.locVar, hlb]; rfl
                simp only [hla, hlb, Option.some.injEq] at htr
                simp only [hae, hbe, Option.some.injEq] at hsem
                obtain rfl := htr
                obtain rfl := hsem
                exact ⟨_, vsimd_step vm V env hc dst.locVar
                  { op := .vsimd op, retTy_eq := rfl,
                    args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }⟩
          · simp [semV, htg] at hsem
      | srl n =>
          rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                rw [← hc a.locVar, hla]; rfl
              simp only [hla, Option.some.injEq] at htr
              simp only [hae, Option.some.injEq] at hsem
              obtain rfl := htr
              obtain rfl := hsem
              exact ⟨_, vsimd_step vm V env hc dst.locVar
                { op := .vpsrldqC n, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }⟩
          · simp [semV, htg] at hsem
      | sll n =>
          rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                rw [← hc a.locVar, hla]; rfl
              simp only [hla, Option.some.injEq] at htr
              simp only [hae, Option.some.injEq] at hsem
              obtain rfl := htr
              obtain rfl := hsem
              exact ⟨_, vsimd_step vm V env hc dst.locVar
                { op := .vpslldqC n, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }⟩
          · simp [semV, htg] at hsem
      | ushuf imm =>
          rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                rw [← hc a.locVar, hla]; rfl
              simp only [hla, Option.some.injEq] at htr
              simp only [hae, Option.some.injEq] at hsem
              obtain rfl := htr
              obtain rfl := hsem
              exact ⟨_, vsimd_step vm V env hc dst.locVar
                { op := .vpshufdC imm, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }⟩
          · simp [semV, htg] at hsem
      | ukeygen rcon =>
          rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                rw [← hc a.locVar, hla]; rfl
              simp only [hla, Option.some.injEq] at htr
              simp only [hae, Option.some.injEq] at hsem
              obtain rfl := htr
              obtain rfl := hsem
              exact ⟨_, vsimd_step vm V env hc dst.locVar
                { op := .vaeskeygenC rcon, retTy_eq := rfl, args := .cons (toVIRVar va) .nil }⟩
          · simp [semV, htg] at hsem
      | vconst val =>
          rcases args with _ | ⟨a, rest⟩
          · simp only [translateDialectControlV, htg, Option.some.injEq] at htr
            simp only [semV, htg, Option.some.injEq] at hsem
            obtain rfl := htr
            obtain rfl := hsem
            exact ⟨_, vsimd_step vm V env hc dst.locVar
              { op := .vconst128 val, retTy_eq := rfl, args := .nil }⟩
          · simp [semV, htg] at hsem
      | sha256rnds2 =>
          rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨cc, _ | ⟨dd, rest⟩⟩⟩⟩
          · simp [semV, htg] at hsem
          · simp [semV, htg] at hsem
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · rcases hlb : lookupReg128 vm b.locVar with _ | vb
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = none := by rw [← hc b.locVar, hlb]; rfl
                simp [hae, hbe] at hsem
              · rcases hlc : lookupReg128 vm cc.locVar with _ | vc
                · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                    rw [← hc a.locVar, hla]; rfl
                  have hbe : env b.locVar = some ((toVIRVar vb).lookup V) := by
                    rw [← hc b.locVar, hlb]; rfl
                  have hce : env cc.locVar = none := by rw [← hc cc.locVar, hlc]; rfl
                  simp [hae, hbe, hce] at hsem
                · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                    rw [← hc a.locVar, hla]; rfl
                  have hbe : env b.locVar = some ((toVIRVar vb).lookup V) := by
                    rw [← hc b.locVar, hlb]; rfl
                  have hce : env cc.locVar = some ((toVIRVar vc).lookup V) := by
                    rw [← hc cc.locVar, hlc]; rfl
                  simp only [hla, hlb, hlc, Option.some.injEq] at htr
                  simp only [hae, hbe, hce, Option.some.injEq] at hsem
                  obtain rfl := htr
                  obtain rfl := hsem
                  exact ⟨_, vsimd_step vm V env hc dst.locVar
                    { op := .vsha256rnds2, retTy_eq := rfl,
                      args := .cons (toVIRVar va) (.cons (toVIRVar vb) (.cons (toVIRVar vc) .nil)) }⟩
          · simp [semV, htg] at hsem
      | sha256msg1 =>
          rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨cc, rest⟩⟩⟩
          · simp [semV, htg] at hsem
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · rcases hlb : lookupReg128 vm b.locVar with _ | vb
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = none := by rw [← hc b.locVar, hlb]; rfl
                simp [hae, hbe] at hsem
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = some ((toVIRVar vb).lookup V) := by
                  rw [← hc b.locVar, hlb]; rfl
                simp only [hla, hlb, Option.some.injEq] at htr
                simp only [hae, hbe, Option.some.injEq] at hsem
                obtain rfl := htr
                obtain rfl := hsem
                exact ⟨_, vsimd_step vm V env hc dst.locVar
                  { op := .vsha256msg1, retTy_eq := rfl,
                    args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }⟩
          · simp [semV, htg] at hsem
      | sha256msg2 =>
          rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨cc, rest⟩⟩⟩
          · simp [semV, htg] at hsem
          · simp [semV, htg] at hsem
          · simp only [translateDialectControlV, htg] at htr
            simp only [semV, htg] at hsem
            rcases hla : lookupReg128 vm a.locVar with _ | va
            · have hae : env a.locVar = none := by rw [← hc a.locVar, hla]; rfl
              simp [hae] at hsem
            · rcases hlb : lookupReg128 vm b.locVar with _ | vb
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = none := by rw [← hc b.locVar, hlb]; rfl
                simp [hae, hbe] at hsem
              · have hae : env a.locVar = some ((toVIRVar va).lookup V) := by
                  rw [← hc a.locVar, hla]; rfl
                have hbe : env b.locVar = some ((toVIRVar vb).lookup V) := by
                  rw [← hc b.locVar, hlb]; rfl
                simp only [hla, hlb, Option.some.injEq] at htr
                simp only [hae, hbe, Option.some.injEq] at hsem
                obtain rfl := htr
                obtain rfl := hsem
                exact ⟨_, vsimd_step vm V env hc dst.locVar
                  { op := .vsha256msg2, retTy_eq := rfl,
                    args := .cons (toVIRVar va) (.cons (toVIRVar vb) .nil) }⟩
          · simp [semV, htg] at hsem
      | loadidx128 =>
          -- `vloadidx128` (128-bit dynamic memref load) is deliberately absent
          -- from `semV` — the SEnv holds only 128-bit register values, so a
          -- memref array + 64-bit index have no `semV` semantics. Hence
          -- `semV c env = none`, contradicting `hsem`; the SEnv homomorphism is
          -- vacuous on this arm (its correctness is the concrete memref-valuation
          -- `Com.denote = spec`, in `FaestByteCombineVsimdCovered`).
          simp [semV, htg] at hsem

end CatCrypt.Crypto.SecureCompilation.Dialects.TranslateDialectVsimd
