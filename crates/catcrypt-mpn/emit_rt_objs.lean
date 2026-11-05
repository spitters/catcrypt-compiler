import CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRuntimeBytesEmit

/-! Writes the verified-encoder objects of `mpn_shift_rt`, `mpn_cmp_ct` and
`mpn_mul_basecase_rt` into this crate's `obj/`. Run from the dev root, the working
directory of every build of the workspace:
`lake env lean --run ../catcrypt-compiler/crates/catcrypt-mpn/emit_rt_objs.lean`. -/

def main : IO Unit :=
  CatCrypt.Crypto.SecureCompilation.X86Backend.MpnRuntimeBytesEmit.emitTo "../catcrypt-compiler/crates/catcrypt-mpn/obj"
