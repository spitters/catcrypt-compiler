pub fn p384_ecdsa_sign(e : &[u8; 48], d : &[u8; 48], k : &[u8; 48], r : &mut [u8; 48], s : &mut [u8; 48], ok : &mut u64) {
    let mut R : [u8; 144] = [0u8; 144];
    let mut x : [u8; 48] = [0u8; 48];
    let mut kinv : [u8; 48] = [0u8; 48];
    let mut rd : [u8; 48] = [0u8; 48];
    let mut erd : [u8; 48] = [0u8; 48];
    let mut vr : u64 = 0;
    let mut vs : u64 = 0;
    p384_scalar_mul_base(&mut R, k);
    p384_point_affine_x(&mut x, &R);
    p384_scalar_reduce(r, &x);
    p384_scalar_inv(&mut kinv, k);
    p384_scalar_muln(&mut rd, &r, d);
    p384_scalar_addn(&mut erd, e, &rd);
    p384_scalar_muln(s, &kinv, &erd);
    p384_scalar_in_range(&mut vr, &r);
    p384_scalar_in_range(&mut vs, &s);
    p384_flag_and(ok, &vr, &vs);
}