pub fn p384_dhkem_encap(skE : &[u8; 48], pkR : &[u8; 97], enc : &mut [u8; 97], ss : &mut [u8; 48], ok : &mut u64) {
    let mut vs : u64 = 0;
    let mut vk : u64 = 0;
    let mut Q : [u8; 144] = [0u8; 144];
    let mut E : [u8; 144] = [0u8; 144];
    let mut Z : [u8; 144] = [0u8; 144];
    let mut dh : [u8; 48] = [0u8; 48];
    let mut ctx : [u8; 194] = [0u8; 194];
    let mut prk : [u8; 48] = [0u8; 48];
    p384_scalar_in_range(&mut vs, skE);
    p384_sec1_valid(&mut vk, pkR);
    p384_sec1_decode(&mut Q, pkR);
    p384_scalar_mul_base(&mut E, skE);
    p384_sec1_encode(enc, &E);
    p384_scalar_mul(&mut Z, skE, &Q);
    p384_dh_x_be(&mut dh, &Z);
    p384_kem_context(&mut ctx, &enc, pkR);
    dhkem_p384_extract(&mut prk, &dh);
    dhkem_p384_expand(ss, &prk, &ctx);
    p384_flag_and(ok, &vs, &vk);
}