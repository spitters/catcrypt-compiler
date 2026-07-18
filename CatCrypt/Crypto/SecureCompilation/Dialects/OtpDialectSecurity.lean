/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative

/-!
# OTP perfect security on `Com catCryptDialect`

The one-time-pad perfect-security guarantee on the crypto dialect: the real and
ideal OTP programs (`CryptoDialectSecurityNative.otpReal_dialect` /
`otpIdeal_dialect`) are at zero statistical distance at every valuation, packaged
both per-valuation and as a single supremum.

The programs are distinct (the real one binds `c = xor(k, m)`, the ideal one
samples directly), and the distance is computed natively through `Com.denoteSP`
and the uniform-sample-XOR bijection — not the valuation-free `Com.all_com_ct`
shadow.
-/

set_option autoImplicit false

namespace CatCrypt.Crypto.SecureCompilation.Dialects.OtpDialectSecurity

open CatCrypt.Core
open CatCrypt.Crypto.SecureCompilation.CryptoSSA (CryptoTy)
open CatCrypt.Crypto.SecureCompilation.VIR
open CatCrypt.Crypto.SecureCompilation.VIR.CatCryptDialect
open CatCrypt.Crypto.SecureCompilation.Dialects.CatCryptDialectSP
open CatCrypt.Crypto.SecureCompilation.Dialects.CryptoDialectSecurityNative
open scoped ENNReal

/-- **Dialect-level OTP perfect security.** The real and ideal one-time-pad
    programs, as `Com catCryptDialect` programs, are at zero statistical distance
    at every valuation: the OTP ciphertext is perfectly indistinguishable from a
    fresh random bit. -/
theorem otp_dialect_perfect_security
    (V : Ctxt.Valuation (d := catCryptDialect) [.bit]) :
    sdist (fun (_ : Unit) => Com.denoteSP otpReal_dialect V)
          (fun (_ : Unit) => Com.denoteSP otpIdeal_dialect V) = 0 :=
  otp_dialect_secure_native V

/-- The supremum-over-valuations OTP security distance is `0` — the single-number
    form mirroring `progSdist`'s shape. -/
theorem otp_dialect_progSdist_zero :
    (⨆ V : Ctxt.Valuation (d := catCryptDialect) [.bit],
        sdist (fun (_ : Unit) => Com.denoteSP otpReal_dialect V)
              (fun (_ : Unit) => Com.denoteSP otpIdeal_dialect V)) = 0 := by
  simp only [otp_dialect_secure_native]
  exact le_antisymm (iSup_le fun _ => le_refl 0) (zero_le)

end CatCrypt.Crypto.SecureCompilation.Dialects.OtpDialectSecurity
