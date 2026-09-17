pub fn p384_ecdsa_verify_msm(u1 : &[u8; 48], G : &[u8; 144], u2 : &[u8; 48], Q : &[u8; 144], __result : &mut [u8; 144]) {
    let mut t1 : [u8; 144] = [0u8; 144];
    let mut t2 : [u8; 144] = [0u8; 144];
    p384_scalar_mul(&mut t1, u1, G);
    p384_scalar_mul(&mut t2, u2, Q);
    p384_point_add(__result, &t1, &t2);
}