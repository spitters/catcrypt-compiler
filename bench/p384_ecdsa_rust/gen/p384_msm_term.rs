pub fn p384_msm_term(k : &[u8; 48], P : &[u8; 144], __result : &mut [u8; 144]) {
    p384_scalar_mul(__result, k, P);
}