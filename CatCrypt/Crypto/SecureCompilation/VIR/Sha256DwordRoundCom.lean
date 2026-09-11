/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-!
# SHA-256 dword compression round on the UNIFIED `Com jasminDialect`

This migrates the SHA-256 32-bit (dword-lane) compression round off the bespoke
`Avx512DwordModel` machine (`ZInstr32D`, `runZBlock32D`, the existing
`Sha256DwordRoundRealization.lean`) onto a hand-authored straight-line
`Com jasminDialect` term over `reg 512` ZMM registers, using the 16×u32 packed
ops `JasminOp.vpackZMMd` (per-lane `VPADDD`/`VPXORD`/`VPANDD`/`VPANDND`) and the
dword right-rotate `JasminOp.vprordZMM` (per-lane `VPRORD`).

The bespoke dword block (`sha256DwordRoundBlock`) computes, per 32-bit lane:

* `Σ₁(e) = ror(e,6) ⊕ ror(e,11) ⊕ ror(e,25)`;
* `Ch(e,f,g) = (e&f) ⊕ ((~e)&g)`;
* `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ`;
* `Σ₀(a) = ror(a,2) ⊕ ror(a,13) ⊕ ror(a,22)`;
* `Maj(a,b,c) = (a&b) ⊕ (a&c) ⊕ (b&c)`;
* `T₂ = Σ₀(a) + Maj(a,b,c)`;
* `a' = T₁ + T₂`, `e' = d + T₁`.

Each bespoke `ZInstr32D` op maps onto a packed dword dialect op:

| `ZInstr32D` op | `vpackZMMd` / `vprordZMM` arm | denote |
|----------------|------------------------------|--------|
| `vpaddd` | `vpackZMMd .add` | `zmmPackD .add` |
| `vpxord` | `vpackZMMd .xor` | `zmmPackD .xor` |
| `vpandd` | `vpackZMMd .and` | `zmmPackD .and` |
| `vprord n` | `vprordZMM n` | `zmmRorD n` |

The bespoke `Ch` complement `~e ⊕ ones; & g` (a `vpxord`+`vpandd` against an
all-ones register) collapses to one `vpackZMMd .andn` (`(~~~e) &&& g`) — the
single-instruction BMI/`VPANDND` form, so the `"ones"` constant register is no
longer needed.

The `*_denote` lemmas pin each Com's denotation to the nested
`zmmPackD`/`zmmRorD` packed expression — the verified-dialect 16×u32 packed
semantics, the packed analogue of the bespoke `aPrimeD`/`ePrimeD`/`t1D`
per-lane math. They are proved by peeling one binding at a time with the
single-layer step lemmas, mirroring `KeccakThetaPiCom.lean`.

Invoke: `lake build CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundCom`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundCom

open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.JasminDialect

/-! ## 1. Register type, contexts, single-binding peel lemmas

A single `reg 512` (one ZMM 16×u32 dword-lane vector) is the working type. -/

/-- The `reg 512` dialect type (one ZMM 16×u32 dword-lane vector), abbreviated. -/
abbrev r512 : JasminTy := .reg 512

/-- **One `vpackZMMd` binding peels to a `zmmPackD` and an extended valuation.** A
    single-layer `rfl`: `Com.denote`'s `.var` arm composed with the `vpackZMMd`
    denote arm. -/
theorem denote_var_vpackZMMd {Γ : Ctxt jasminDialect} {s : JasminTy}
    (bop : JasminBinOp) (va vb : Ctxt.Var Γ r512)
    (body : Com jasminDialect (r512 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (JasminOp.vpackZMMd bop) rfl (.cons va (.cons vb .nil))) body).denote V
      = body.denote (V.extend (zmmPackD bop (va.lookup V) (vb.lookup V))) :=
  rfl

/-- **One `vprordZMM` binding peels to a `zmmRorD` and an extended valuation.** A
    single-layer `rfl`: `Com.denote`'s `.var` arm composed with the `vprordZMM`
    denote arm. -/
theorem denote_var_vprordZMM {Γ : Ctxt jasminDialect} {s : JasminTy}
    (n : Nat) (va : Ctxt.Var Γ r512)
    (body : Com jasminDialect (r512 :: Γ) s) (V : Ctxt.Valuation Γ) :
    (Com.var (Expr.mk (JasminOp.vprordZMM n) rfl (.cons va .nil)) body).denote V
      = body.denote (V.extend (zmmRorD n (va.lookup V))) :=
  rfl

/-- `Ctxt.Var.here.lookup` on an extended valuation reads the freshly bound head. -/
@[simp] theorem lookup_here_extend {Γ : Ctxt jasminDialect} {t : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t⟧) :
    (Ctxt.Var.here (Γ := Γ) (t := t)).lookup (V.extend v) = v := rfl

/-- `(Ctxt.Var.there w).lookup` on an extended valuation skips the head. -/
@[simp] theorem lookup_there_extend {Γ : Ctxt jasminDialect} {t t' : JasminTy}
    (V : Ctxt.Valuation Γ) (v : ⟦t'⟧) (w : Ctxt.Var Γ t) :
    (Ctxt.Var.there (s := t') w).lookup (V.extend v) = w.lookup V := rfl

/-! ## 2. The input context and the per-lane packed spec

The eight working words `a … h` plus the round constant `Kₜ` and schedule word
`Wₜ`, each a `reg 512` ZMM (16 independent SHA-256 lanes per register). De Bruijn
order: `wa = 0, wb = 1, …, wh = 7, kt = 8, wt = 9`. -/

/-- The SHA-256 dword round input context `[wa,wb,wc,wd,we,wf,wg,wh,kt,wt]`. -/
abbrev roundCtx : Ctxt jasminDialect :=
  [r512, r512, r512, r512, r512, r512, r512, r512, r512, r512]

/-- Packed `Σ₁(e) = ror(e,6) ⊕ ror(e,11) ⊕ ror(e,25)` (16×u32, `zmmRorD`/`zmmPackD .xor`). -/
def sig1Packed (we : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .xor (zmmRorD 6 we) (zmmRorD 11 we)) (zmmRorD 25 we)

/-- Packed `Ch(e,f,g) = (e&f) ⊕ ((~e)&g)` (`zmmPackD .and`/`.andn`/`.xor`). -/
def chPacked (we wf wg : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .and we wf) (zmmPackD .andn we wg)

/-- Packed `T₁ = h + Σ₁(e) + Ch(e,f,g) + Kₜ + Wₜ` (four `zmmPackD .add`). -/
def t1Packed (we wf wg wh kt wt : BitVec 512) : BitVec 512 :=
  zmmPackD .add
    (zmmPackD .add (zmmPackD .add (zmmPackD .add wh (sig1Packed we)) (chPacked we wf wg)) kt)
    wt

/-- Packed `Σ₀(a) = ror(a,2) ⊕ ror(a,13) ⊕ ror(a,22)`. -/
def sig0Packed (wa : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .xor (zmmRorD 2 wa) (zmmRorD 13 wa)) (zmmRorD 22 wa)

/-- Packed `Maj(a,b,c) = (a&b) ⊕ (a&c) ⊕ (b&c)`. -/
def majPacked (wa wb wc : BitVec 512) : BitVec 512 :=
  zmmPackD .xor (zmmPackD .xor (zmmPackD .and wa wb) (zmmPackD .and wa wc))
    (zmmPackD .and wb wc)

/-- Packed `a' = T₁ + (Σ₀(a) + Maj(a,b,c))`. -/
def aPrimePacked (wa wb wc we wf wg wh kt wt : BitVec 512) : BitVec 512 :=
  zmmPackD .add (t1Packed we wf wg wh kt wt)
    (zmmPackD .add (sig0Packed wa) (majPacked wa wb wc))

/-- Packed `e' = d + T₁`. -/
def ePrimePacked (wd we wf wg wh kt wt : BitVec 512) : BitVec 512 :=
  zmmPackD .add wd (t1Packed we wf wg wh kt wt)

/-! ## 3. The dword round `Com` and its denotation pins

We build two single-output `Com`s — one returning `a'`, one returning `e'`. Each
threads the SHA-256 round dataflow as a straight-line `vpackZMMd`/`vprordZMM`
nest; the de Bruijn indices shift as bindings are pushed. -/

/-- The dword round `a' = T₁ + (Σ₀(a) + Maj)` as a `Com jasminDialect`. -/
def aPrimeCom : Com jasminDialect roundCtx r512 :=
  -- Σ₁(e): we = idx4
  .var (.mk (.vprordZMM 6) rfl (.cons (.there (.there (.there (.there .here)))) .nil))  -- e6
  (.var (.mk (.vprordZMM 11) rfl (.cons (.there (.there (.there (.there (.there .here))))) .nil))  -- e11; we now idx5
  (.var (.mk (.vprordZMM 25) rfl (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))  -- e25; we now idx6
  -- ex = e6 ^ e11 ; under [e25,e11,e6,wa..wt]: e6 idx2, e11 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- sig1 = ex ^ e25 ; under [ex,e25,e11,e6,...]: ex idx0, e25 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons .here (.cons (.there .here) .nil)))
  -- Ch: under [sig1,ex,e25,e11,e6, wa(5)..wt(14)]. we idx9, wf idx10, wg idx11
  -- ef = we & wf
  (.var (.mk (.vpackZMMd .and) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                                      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))  .nil)))
  -- eng = (~we) & wg ; under [ef,sig1,ex,e25,e11,e6, wa(6)..wt(15)]. we idx10, wg idx12
  (.var (.mk (.vpackZMMd .andn) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                                       (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)))
  -- chr = ef ^ eng ; under [eng,ef,sig1,...]: ef idx1, eng idx0
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there .here) (.cons .here .nil)))
  -- T1: under [chr,eng,ef,sig1,ex,e25,e11,e6, wa(8)..wt(17)]. wh idx15, sig1 idx3, chr idx0, kt idx16, wt idx17
  -- t1a = wh + sig1
  (.var (.mk (.vpackZMMd .add) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
                                      (.cons (.there (.there (.there .here))) .nil)))
  -- t1b = t1a + chr ; under [t1a,chr,...]: t1a idx0, chr idx1
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there .here) .nil)))
  -- t1c = t1b + kt ; under [t1b,t1a,chr,eng,ef,sig1,ex,e25,e11,e6, wa(10)..wt(19)]. kt idx18
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)))
  -- t1 = t1c + wt ; under [t1c,t1b,...]: t1c idx0, wt idx20
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)))
  -- Σ₀(a): under [t1,t1c,t1b,t1a,chr,eng,ef,sig1,ex,e25,e11,e6, wa(12)..wt(21)]. wa idx12
  (.var (.mk (.vprordZMM 2) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil))  -- a2; wa now idx13
  (.var (.mk (.vprordZMM 13) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil))  -- a13; wa now idx14
  (.var (.mk (.vprordZMM 22) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil))  -- a22; wa now idx15
  -- ax = a2 ^ a13 ; under [a22,a13,a2,t1,...]: a2 idx2, a13 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- sig0 = ax ^ a22 ; under [ax,a22,a13,a2,...]: ax idx0, a22 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons .here (.cons (.there .here) .nil)))
  -- Maj: under [sig0,ax,a22,a13,a2,t1,t1c,t1b,t1a,chr,eng,ef,sig1,ex,e25,e11,e6, wa(17)..wt(26)]
  -- wa idx17, wb idx18, wc idx19
  -- ab = wa & wb
  (.var (.mk (.vpackZMMd .and) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))
                                      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))  .nil)))
  -- ac = wa & wc ; under [ab,sig0,...]: wa idx18, wc idx20
  (.var (.mk (.vpackZMMd .and) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))
                                      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)))
  -- bc = wb & wc ; under [ac,ab,sig0,...]: wb idx20, wc idx21
  (.var (.mk (.vpackZMMd .and) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))
                                      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))  .nil)))
  -- mx = ab ^ ac ; under [bc,ac,ab,sig0,...]: ab idx2, ac idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- majr = mx ^ bc ; under [mx,bc,ac,ab,sig0,...]: mx idx0, bc idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons .here (.cons (.there .here) .nil)))
  -- t2 = sig0 + majr ; under [majr,mx,bc,ac,ab,sig0,ax,a22,a13,a2,t1,...]: sig0 idx5, majr idx0
  (.var (.mk (.vpackZMMd .add) rfl (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil)))
  -- a' = t1 + t2 ; under [t2,majr,mx,bc,ac,ab,sig0,ax,a22,a13,a2,t1,...]: t1 idx11, t2 idx0
  (.var (.mk (.vpackZMMd .add) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)))
  (.ret .here))))))))))))))))))))))))

/-- The dword round `e' = d + T₁` as a `Com jasminDialect`. -/
def ePrimeCom : Com jasminDialect roundCtx r512 :=
  -- Σ₁(e): we = idx4
  .var (.mk (.vprordZMM 6) rfl (.cons (.there (.there (.there (.there .here)))) .nil))  -- e6
  (.var (.mk (.vprordZMM 11) rfl (.cons (.there (.there (.there (.there (.there .here))))) .nil))  -- e11; we idx5
  (.var (.mk (.vprordZMM 25) rfl (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))  -- e25; we idx6
  -- ex = e6 ^ e11 ; e6 idx2, e11 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there (.there .here)) (.cons (.there .here) .nil)))
  -- sig1 = ex ^ e25 ; ex idx0, e25 idx1
  (.var (.mk (.vpackZMMd .xor) rfl (.cons .here (.cons (.there .here) .nil)))
  -- Ch: under [sig1,ex,e25,e11,e6, wa(5)..wt(14)]. we idx9, wf idx10, wg idx11
  -- ef = we & wf
  (.var (.mk (.vpackZMMd .and) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))
                                      (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))  .nil)))
  -- eng = (~we) & wg ; under [ef,sig1,...]: we idx10, wg idx12
  (.var (.mk (.vpackZMMd .andn) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
                                       (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)))
  -- chr = ef ^ eng ; ef idx1, eng idx0
  (.var (.mk (.vpackZMMd .xor) rfl (.cons (.there .here) (.cons .here .nil)))
  -- t1a = wh + sig1 ; under [chr,eng,ef,sig1,ex,e25,e11,e6, wa(8)..wt(17)]. wh idx15, sig1 idx3
  (.var (.mk (.vpackZMMd .add) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
                                      (.cons (.there (.there (.there .here))) .nil)))
  -- t1b = t1a + chr ; t1a idx0, chr idx1
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there .here) .nil)))
  -- t1c = t1b + kt ; under [t1b,t1a,chr,eng,ef,sig1,ex,e25,e11,e6, wa(10)..wt(19)]. kt idx18
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)))
  -- t1 = t1c + wt ; t1c idx0, wt idx20
  (.var (.mk (.vpackZMMd .add) rfl (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil)))
  -- e' = wd + t1 ; under [t1,t1c,t1b,t1a,chr,eng,ef,sig1,ex,e25,e11,e6, wa(12)..wt(21)]. wd idx15, t1 idx0
  (.var (.mk (.vpackZMMd .add) rfl (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))
                                      (.cons .here .nil)))
  (.ret .here)))))))))))))

/-! ## 4. Denotation pins -/

/-- **Dword round `a'` denotation pin.** On any working-word valuation
    `⟨wa,wb,wc,wd,we,wf,wg,wh,kt,wt⟩`, `aPrimeCom` denotes to `aPrimePacked …` —
    the verified-dialect 16×u32 packed `a' = T₁ + (Σ₀(a) + Maj(a,b,c))`, the
    packed analogue of the bespoke `aPrimeD` per-lane round output. -/
theorem aPrimeCom_denote
    (wa wb wc wd we wf wg wh kt wt : BitVec 512) :
    aPrimeCom.denote (.cons wa (.cons wb (.cons wc (.cons wd (.cons we (.cons wf
      (.cons wg (.cons wh (.cons kt (.cons wt .nil)))))))))) =
      aPrimePacked wa wb wc we wf wg wh kt wt := by
  simp only [aPrimeCom, denote_var_vpackZMMd, denote_var_vprordZMM,
    lookup_here_extend, lookup_there_extend]
  rfl

/-- **Dword round `e'` denotation pin.** On any working-word valuation, `ePrimeCom`
    denotes to `ePrimePacked …` — the verified-dialect 16×u32 packed `e' = d + T₁`,
    the packed analogue of the bespoke `ePrimeD`. -/
theorem ePrimeCom_denote
    (wa wb wc wd we wf wg wh kt wt : BitVec 512) :
    ePrimeCom.denote (.cons wa (.cons wb (.cons wc (.cons wd (.cons we (.cons wf
      (.cons wg (.cons wh (.cons kt (.cons wt .nil)))))))))) =
      ePrimePacked wd we wf wg wh kt wt := by
  simp only [ePrimeCom, denote_var_vpackZMMd, denote_var_vprordZMM,
    lookup_here_extend, lookup_there_extend]
  rfl

/-- **The migrated SHA-256 dword round computes `a'`/`e'` in the verified
    `Com jasminDialect`.** Both Com programs denote to the verified-dialect
    16×u32 packed round outputs, mirroring the bespoke `aPrimeD`/`ePrimeD`. -/
theorem sha256DwordRoundCom_realizes
    (wa wb wc wd we wf wg wh kt wt : BitVec 512) :
    aPrimeCom.denote (.cons wa (.cons wb (.cons wc (.cons wd (.cons we (.cons wf
        (.cons wg (.cons wh (.cons kt (.cons wt .nil))))))))))
        = aPrimePacked wa wb wc we wf wg wh kt wt
      ∧ ePrimeCom.denote (.cons wa (.cons wb (.cons wc (.cons wd (.cons we (.cons wf
        (.cons wg (.cons wh (.cons kt (.cons wt .nil))))))))))
        = ePrimePacked wd we wf wg wh kt wt :=
  ⟨aPrimeCom_denote wa wb wc wd we wf wg wh kt wt,
   ePrimeCom_denote wa wb wc wd we wf wg wh kt wt⟩

end CatCrypt.Crypto.SecureCompilation.VIR.Sha256DwordRoundCom
