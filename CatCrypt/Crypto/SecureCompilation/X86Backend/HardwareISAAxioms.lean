/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public meta import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
public import CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
public meta import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
public import CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit

/-!
# The factored hardware-ISA trust boundary for the emit pipeline

The verified emit pipeline lowers a typed AST through `LowCT → catCryptDialect →
Com → jasmin`, bottoming out in a small set of **hardware crypto/arithmetic
instructions** used as leaves: SHA-NI, AES-NI, VAES, GFNI, PCLMUL, ADX, BMI2.
The correctness of each such leaf — that the silicon computes its documented
function — is a *trust assumption* the pipeline rests on; it cannot be discharged
inside Lean, only validated against an external authoritative semantics.

The opaque jasmin leaf symbols (`Jasmin.LowCTReflect.shani_sha256_rnds2`,
`vaesenc_2way`, `vpclmul_qdq_carryless_mul`, …) carry their semantics in
prose docstrings ("per the Intel SDM", "pinned by the HACL* KAT"). This module is
the single place that lists *exactly which* hardware facts the pipeline depends
on and *how strongly* each is validated. It **factors** the trust boundary into one
explicit record per hardware-instruction family
(`HardwareLeafFamily`), each carrying:

* **(a) what it asserts** — the owned-model leaf denotation equals its ISA spec;
* **(b) discharge status** — whether the family is anchored to the
  [`rems-project/sail-x86-from-acl2`] Sail-x86 model (`Tier.sailAnchored`), to
  the FIPS-180-4 standard directly (`Tier.fipsClosed`, SHA-NI only), or is
  irreducible/spec-self-transcribed (`Tier.sdmTranscribed`, ADX/BMI2);
* **(c) the validation story** — the differential check that backs the tier.

The *witnesses* are the already-proven theorems from `SailX86Lean.lean`
(the `*_eq_sail*` leaf identities) and `ShaNiEmit.lean` (the FIPS-180-4 round
bridge). This module does **not** introduce new opaque hypotheses; it collects
the existing anchors into an auditable surface and records which families are
validatable-against-an-independent-semantics versus pinned-to-the-SDM-only.

## The scalar SHA-256 ↔ FIPS-180-4 baseline (CLOSED)

Independently of the hardware leaves, the *scalar* SHA-256/512 emit path is
**closed** to FIPS-180-4 with no residual hypothesis:
`Sha2EmitterReadoutHalf.emitRound_initEnv_eq_fips_sha256_unconditional` is an
unconditional theorem (KAT-free, no `native_decide`) — the emitted round, on a
faithful runtime store, denotes bit-exactly to `fipsRound sha256Spec`. The
`EmitRoundDenotesClosedFormFaithful_holds` Prop is inhabited as a theorem, so
the FIPS bridge carries no leaf assumption at all. The hardware-leaf surface
below is therefore orthogonal: it concerns the SHA-NI / AES-NI / … *intrinsic*
leaves, not the scalar lowering.

## Tier semantics

The three tiers are a **strict ordering of validation strength**, not cosmetic:

* `Tier.fipsClosed` (SHA-NI) — the owned leaf denotation is *definitionally*
  (`rfl`) the FIPS-180-4 SHA-256 round body. There is nothing left to trust
  about the *value* the instruction computes beyond "the silicon implements
  `SHA256RNDS2` per the SDM, which the SDM *defines* as the FIPS round". This is
  the strongest tier: the spec the leaf is pinned to is the cryptographic
  standard itself.

* `Tier.sailAnchored` (AES-NI / VAES / GFNI / PCLMUL) — the owned leaf
  denotation equals a Sail-x86 spec function, cross-checked on FIPS-197 / GHASH
  **known-answer vectors** run through the Sail `0.20.1` interpreter. The
  Sail-x86 model is the ACL2 `x86isa` reference (Goel/Hunt/Kaufmann),
  *independent* of Jasmin's Rocq model. (The upstream ACL2 corpus predates
  these extensions, so the spec functions were SDM/FIPS-197-transcribed on the
  Sail side; but the KAT cross-check ties them to the published FIPS-197
  answers, an independent oracle.)

* `Tier.sdmTranscribed` (ADX: ADCX/ADOX — BMI2: MULX/RORX) — **irreducible.**
  The upstream ACL2 `x86isa` model has *no* ADX/BMI2 instructions, and
  no other independent executable x86 reference models them either, so there is
  no oracle to differentially validate against beyond the Intel SDM text. The
  owned leaf is pinned to an SDM-transcribed Sail spec (`mulx_eq_sail*` /
  `adcx_eq_sail*` / `adox_eq_sail*` in `SailX86Lean.lean`) and gas-validated at
  the byte level, but this is a *self-consistency* check against our own
  SDM transcription, not agreement with an independent corpus. This tier is a
  **ceiling**, documented as not-further-reducible — do not re-attempt to derive
  it from an ACL2/Sail model that does not contain these instructions.

Each family below names its discharge witness theorem(s); a reader auditing the
emit pipeline's hardware-trust footprint can read this file top to bottom.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.X86Backend.HardwareISA

open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
open CatCrypt.Crypto.SecureCompilation.VIR

/-! ## 1. The validation tier -/

/-- The validation strength backing a hardware-leaf family's spec anchor.
    Strictly ordered: `fipsClosed > sailAnchored > sdmTranscribed`. -/
inductive Tier where
  /-- Owned leaf denotation is *definitionally* the FIPS-180-4 round body
      (SHA-NI). The leaf is pinned to the cryptographic standard itself. -/
  | fipsClosed
  /-- Owned leaf denotation equals a Sail-x86 (ACL2 `x86isa`) spec function,
      cross-checked on FIPS-197 / GHASH known-answer vectors through the Sail
      interpreter (AES-NI / VAES / GFNI / PCLMUL). -/
  | sailAnchored
  /-- Owned leaf pinned to an SDM-transcribed Sail spec only; **irreducible**
      (no independent ACL2/Sail corpus for ADX/BMI2). A ceiling. -/
  | sdmTranscribed
deriving DecidableEq, Repr

/-- Is this tier discharged against a semantics *independent* of our own SDM
    transcription? `fipsClosed` and `sailAnchored` are (FIPS standard / FIPS-197
    KAT); `sdmTranscribed` is not (self-consistency only). -/
def Tier.independentlyValidated : Tier → Bool
  | .fipsClosed     => true
  | .sailAnchored   => true
  | .sdmTranscribed => false

/-! ## 2. The per-family trust record

Each `HardwareLeafFamily` names the instruction family, the owned leaves it
covers, its validation tier, and a prose pointer to the discharge witness(es).
The `validated := tier.independentlyValidated` field makes the auditable
distinction explicit as data. -/

/-- One entry in the factored hardware-ISA trust surface. -/
structure HardwareLeafFamily where
  /-- The ISA family name (e.g. `"SHA-NI"`). -/
  family : String
  /-- The instruction mnemonics in the family. -/
  mnemonics : List String
  /-- (a) What the leaf-correctness assumption asserts, in one line. -/
  asserts : String
  /-- (b) The validation tier. -/
  tier : Tier
  /-- (c) The discharge witness theorem name(s) (validation story pointer). -/
  witness : String
  /-- Derived: discharged against an independent semantics (not self-SDM). -/
  validated : Bool := tier.independentlyValidated
deriving Repr

/-! ## 3. The trust surface, one record per family

These are the *only* hardware-instruction families the emit pipeline uses as
leaves. The list is exhaustive for the crypto/bignum kernels.  -/

/-- **SHA-NI** — `SHA256RNDS2` / `SHA256MSG1` / `SHA256MSG2`.
    `Tier.fipsClosed`: the owned `ShaNiEmit.sha256rnds2_lane` (and the two msg
    lanes) denote *definitionally* (`rfl`) to the FIPS-180-4 SHA-256 round body
    — `sha256rnds2_eq_sha256_round_pair`, `sha256msg1_eq_sigma0_partial`,
    `sha256msg2_eq_sigma1_completion`. -/
def shaNi : HardwareLeafFamily where
  family := "SHA-NI"
  mnemonics := ["SHA256RNDS2", "SHA256MSG1", "SHA256MSG2"]
  asserts :=
    "the SHA-NI leaf denotation = FIPS-180-4 SHA-256 round/message-schedule body"
  tier := .fipsClosed
  witness :=
    "ShaNiEmit.sha256rnds2_eq_sha256_round_pair / sha256msg1_eq_sigma0_partial \
     / sha256msg2_eq_sigma1_completion (all rfl); orthogonal scalar baseline \
     Sha2EmitterReadoutHalf.emitRound_initEnv_eq_fips_sha256_unconditional"

/-- **AES-NI** — `AESENC` / `AESENCLAST` / `AESKEYGENASSIST`.
    `Tier.sailAnchored`: owned `Jasmin.wAESENC` / `wAESENCLAST` /
    `wAESKEYGENASSIST` = Sail-x86 `aesenc_spec` / `aesenclast_spec` /
    `aeskeygenassist_spec` on the FIPS-197 worked-example block. -/
def aesNi : HardwareLeafFamily where
  family := "AES-NI"
  mnemonics := ["AESENC", "AESENCLAST", "AESKEYGENASSIST"]
  asserts := "the AES-NI leaf denotation = Sail-x86 aes*_spec (FIPS-197 round)"
  tier := .sailAnchored
  witness :=
    "SailX86Lean.aesenc_eq_sail / aesenclast_eq_sail / aeskeygenassist_eq_sail \
     / aesenc_zerokey_eq_sail"

/-- **VAES** — VEX/EVEX `VAESENC` / `VAESENCLAST` (per-128-bit-lane).
    `Tier.sailAnchored`: each 128-bit lane is exactly the AES-NI round, so the
    AES-NI Sail identities are the per-lane VAES anchor (the only difference is
    the VEX/EVEX *encoding*, validated in `CryptoExtValidation.lean`). -/
def vaes : HardwareLeafFamily where
  family := "VAES"
  mnemonics := ["VAESENC", "VAESENCLAST", "VAESDEC", "VAESDECLAST"]
  asserts := "the VAES per-lane denotation = AES-NI round = Sail-x86 aes*_spec"
  tier := .sailAnchored
  witness :=
    "SailX86Lean.aesenc_eq_sail / aesenclast_eq_sail (per-lane); \
     CryptoExtValidation encodeVaes byte pins"

/-- **GFNI** — `GF2P8MULB` / `GF2P8AFFINEQB` (+ VEX `V*` forms).
    `Tier.sailAnchored`: owned `gf28_byte_mul` / `vgf2p8mulb_128` = Sail-x86
    `gf256_mul` on FIPS-197 example bytes + classic AES inverse pairs. -/
def gfni : HardwareLeafFamily where
  family := "GFNI"
  mnemonics := ["GF2P8MULB", "GF2P8AFFINEQB", "VGF2P8MULB", "VGF2P8AFFINEQB"]
  asserts := "the GFNI byte/lane denotation = Sail-x86 gf256_mul (GF(2^8) mod 0x11B)"
  tier := .sailAnchored
  witness :=
    "SailX86Lean.gf256_mul_eq_sail_fips / gf256_mul_eq_sail_pairs / gf2p8mulb_eq_sail"

/-- **PCLMUL** — `PCLMULQDQ` / `VPCLMULQDQ`.
    `Tier.sailAnchored`: owned `VPClmulEmit.polyMul64` = Sail-x86 `clmul64_spec`
    (the carry-less GF(2)[x] 64×64→128 product) on GHASH-style KAT vectors. -/
def pclmul : HardwareLeafFamily where
  family := "PCLMUL"
  mnemonics := ["PCLMULQDQ", "VPCLMULQDQ"]
  asserts := "the PCLMUL denotation = Sail-x86 clmul64_spec (carry-less mul)"
  tier := .sailAnchored
  witness :=
    "SailX86Lean.clmul_eq_sail_small / clmul_eq_sail_ff / clmul_eq_sail_max"

/-- **ADX** — `ADCX` / `ADOX` (independent dual carry chains).
    `Tier.sdmTranscribed` (**irreducible**): the upstream ACL2 `x86isa`
    model has no ADX, so `adcx_adox_spec_64` is SDM-transcribed on the Sail
    side. Owned `evalInstr .adcx`/`.adox` = that spec, with the defining
    flag-routing (`ADCX→CF`, `ADOX→OF`). No independent corpus exists to
    cross-validate against — this is a ceiling. -/
def adx : HardwareLeafFamily where
  family := "ADX"
  mnemonics := ["ADCX", "ADOX"]
  asserts :=
    "the ADX leaf = SDM adcx_adox_spec_64 with ADCX→CF / ADOX→OF flag routing"
  tier := .sdmTranscribed
  witness :=
    "SailX86Lean.adcx_eq_sail₁₋₃ / adox_eq_sail₁₋₃ / adcx_adox_same_value \
     (SDM-transcribed Sail; gas byte-validated; irreducible)"

/-- **BMI2** — `MULX` (widening multiply, no flags) / `RORX`.
    `Tier.sdmTranscribed` (**irreducible**): like ADX, absent from the
    upstream ACL2 model; owned `evalInstr .mulx` = SDM-transcribed
    `mulx_spec_64`. The widening *product* is additionally cross-checked via the
    unsigned `MUL` (`mul_spec_64`), which the ACL2 model *does* contain — so the
    `(hi,lo)` value is independently anchored, but the BMI2 *form/encoding* is
    SDM-only. -/
def bmi2 : HardwareLeafFamily where
  family := "BMI2"
  mnemonics := ["MULX", "RORX"]
  asserts :=
    "the MULX leaf = SDM mulx_spec_64 (= unsigned MUL product split (lo,hi))"
  tier := .sdmTranscribed
  witness :=
    "SailX86Lean.mulx_eq_sail₁₋₄ (SDM-transcribed Sail; product cross-checked \
     via ACL2 mul_spec_64 in SailX86Validation.sail_mulx_via_mul_*; \
     irreducible form)"

/-- The complete factored hardware-ISA trust surface: every instruction family
    the emit pipeline uses as a leaf, with its discharge tier and witness. -/
def hardwareTrustSurface : List HardwareLeafFamily :=
  [shaNi, aesNi, vaes, gfni, pclmul, adx, bmi2]

/-! ## 4. Surface-level audit facts

These `theorem`s let `audit_security.lean` (and a human reader) confirm the
shape of the surface without re-reading the prose. -/

/-- The surface has exactly the seven hardware-leaf families. -/
theorem surface_card : hardwareTrustSurface.length = 7 := by decide

/-- The independently-validated families (FIPS-closed or Sail-anchored) are
    SHA-NI, AES-NI, VAES, GFNI, PCLMUL. -/
theorem independently_validated_families :
    ((hardwareTrustSurface.filter (·.validated)).map (·.family))
      = ["SHA-NI", "AES-NI", "VAES", "GFNI", "PCLMUL"] := by decide

/-- The irreducible (SDM-transcribed) families are exactly ADX and BMI2. -/
theorem irreducible_families :
    ((hardwareTrustSurface.filter (fun f => ! f.validated)).map (·.family))
      = ["ADX", "BMI2"] := by decide

/-- SHA-NI is the unique `fipsClosed` family. -/
theorem shaNi_is_fipsClosed :
    ((hardwareTrustSurface.filter (·.tier == Tier.fipsClosed)).map (·.family))
      = ["SHA-NI"] := by decide

/-! ## 5. Discharge witnesses, re-exported as the auditable anchor

The factored records above carry the witness theorem *names*; here we re-export
the witnesses themselves so that anyone importing this module gets the proven
leaf identities directly — the trust boundary is `import`-visible, not
prose-only. (These are the already-proven theorems; this section adds no new
content beyond making them reachable through the surface module.) -/

section Witnesses
open CatCrypt.Crypto.SecureCompilation.X86Backend.SailX86Lean
open CatCrypt.Crypto.SecureCompilation.X86Backend.Jasmin
open CatCrypt.Crypto.SecureCompilation.VIR.ShaNiEmit
open CatCrypt.Crypto.Jasmin
open CatCrypt.Crypto.SecureCompilation.MLIR.VectorDialect.X86Intrinsics
open CatCrypt.Crypto.SecureCompilation.VIR.VPClmulEmit

/-- **SHA-NI discharge** (FIPS-closed): the `SHA256RNDS2` owned leaf denotes
    *definitionally* to two FIPS-180-4 SHA-256 compression rounds. Re-export of
    `ShaNiEmit.sha256rnds2_eq_sha256_round_pair`. -/
theorem shaNi_discharge (abef cdgh mk : BitVec 128) :
    sha256rnds2_lane abef cdgh mk =
      (let (a, b, e, f) := unpackABEF abef
       let (c, d, g, h) := unpackCDGH cdgh
       let mk0 := laneOf128 mk 0
       let mk1 := laneOf128 mk 1
       let (a', b', _c', _d', e', f', _g', _h') :=
         sha256RoundFunc.compose_two (a, b, c, d, e, f, g, h) mk0 mk1
       packABEF a' b' e' f') :=
  sha256rnds2_eq_sha256_round_pair abef cdgh mk

/-- **AES-NI discharge** (Sail-anchored): owned `wAESENC` = Sail `aesenc_spec`
    on the FIPS-197 block. Re-export of `SailX86Lean.aesenc_eq_sail`. -/
theorem aesNi_discharge :
    wAESENC fipsBlk fipsKey = 0xe7bbd0de82cc798722c5e80b9f93215b#128 :=
  aesenc_eq_sail

/-- **GFNI discharge** (Sail-anchored): owned `gf28_byte_mul` = Sail `gf256_mul`
    on the FIPS-197 example bytes. Re-export of `SailX86Lean.gf256_mul_eq_sail_fips`. -/
theorem gfni_discharge :
    gf28_byte_mul 0x57#8 0x83#8 = sailGf256Mul 0x57#8 0x83#8 ∧
    gf28_byte_mul 0x57#8 0x13#8 = sailGf256Mul 0x57#8 0x13#8 :=
  gf256_mul_eq_sail_fips

/-- **PCLMUL discharge** (Sail-anchored): owned `polyMul64` = Sail `clmul64_spec`.
    Re-export of `SailX86Lean.clmul_eq_sail_small`. -/
theorem pclmul_discharge :
    polyMul64 0x3#64 0x3#64 = 5#128 ∧ polyMul64 1#64 1#64 = 1#128 :=
  clmul_eq_sail_small

/-- **BMI2 `MULX` discharge** (SDM-transcribed, product cross-checked via
    ACL2 `mul_spec_64`): owned `.mulx` words = Sail `mulx_spec_64`. Re-export of
    `SailX86Lean.mulx_eq_sail₂`. -/
theorem bmi2_mulx_discharge :
    let s := evalInstr (jstMul 1311768467463790320 18364758544493064720)
                       (.mulx "hi" "lo" (.reg "a") (.reg "b"))
    (s.get "lo", s.get "hi")
      = sailMulx 1311768467463790320 18364758544493064720 :=
  mulx_eq_sail₂

/-- **ADX `ADCX` discharge** (SDM-transcribed, irreducible): owned
    `.adcx` = Sail `adcx_adox_spec_64`, carry routed to `CF`, `OF` untouched.
    Re-export of `SailX86Lean.adcx_eq_sail₁`. -/
theorem adx_adcx_discharge :
    let s := evalInstr (jstC 5 true) (.adcx "a" (.imm 8))
    (s.get "a", s.flags.cf.getD false) = sailAdcxAdox 5 8 true ∧
    s.flags.of = none :=
  adcx_eq_sail₁

end Witnesses

end CatCrypt.Crypto.SecureCompilation.X86Backend.HardwareISA
