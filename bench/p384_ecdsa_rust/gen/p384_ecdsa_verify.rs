pub fn p384_ecdsa_verify(e : &[u8; 48], r : &[u8; 48], s : &[u8; 48], Q : &[u8; 144], ok : &mut u64) {
    let mut vr : u64 = 0;
    let mut vs : u64 = 0;
    let mut vq : u64 = 0;
    let mut sinv : [u8; 48] = [0u8; 48];
    let mut u1 : [u8; 48] = [0u8; 48];
    let mut u2 : [u8; 48] = [0u8; 48];
    let mut R : [u8; 144] = [0u8; 144];
    let mut x : [u8; 48] = [0u8; 48];
    let mut xn : [u8; 48] = [0u8; 48];
    let mut eq : u64 = 0;
    let mut c1 : u64 = 0;
    let mut c2 : u64 = 0;
    p384_scalar_in_range(&mut vr, r);
    p384_scalar_in_range(&mut vs, s);
    p384_point_valid(&mut vq, Q);
    p384_scalar_inv(&mut sinv, s);
    p384_scalar_muln(&mut u1, e, &sinv);
    p384_scalar_muln(&mut u2, r, &sinv);
    p384_lincomb(&mut R, &u1, &u2, Q);
    p384_point_affine_x(&mut x, &R);
    p384_scalar_reduce(&mut xn, &x);
    p384_scalar_is_eq(&mut eq, &xn, r);
    p384_flag_and(&mut c1, &vr, &vs);
    p384_flag_and(&mut c2, &c1, &vq);
    p384_flag_and(ok, &c2, &eq);
}