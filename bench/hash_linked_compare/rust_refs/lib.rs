//! Rust BLAKE2b peers of `bench/hash_linked_compare`, called from `compare.c`.
//!
//! RustCrypto `blake2` 0.10.6 (unverified, portable Rust): `rc_blake2b_*` hold a
//! `Blake2bVarCore` with a 64-byte output. `rc_blake2b_update_block` is one call of
//! `UpdateCore::update_blocks` on one 128-byte block: the counter advances by 128 and the
//! compression runs with the finalisation flag clear, the work of one compression.
//!
//! libcrux `libcrux-blake2` (Rust generated from HACL*, verified): `lc_blake2b_*` hold a
//! streaming state with a 64-byte digest. `lc_blake2b_update_block` is one `update` of 128
//! bytes; the streaming state keeps the last block in its buffer until more input arrives,
//! so each call copies the block into the buffer and compresses the previous one.
//!
//! Both crates expose no compression with a caller-given chaining value, counter and flag, so
//! their conformance is checked on whole BLAKE2b-512 digests (`rc_blake2b512`,
//! `lc_blake2b512`) and their timing arms run on their own state.

use blake2::digest::core_api::{Block, UpdateCore, VariableOutputCore};
use blake2::digest::Digest;
use blake2::{Blake2b512, Blake2bVarCore};
use libcrux_blake2::Blake2bBuilder;

/// A fresh RustCrypto BLAKE2b core with a 64-byte output.
#[no_mangle]
pub extern "C" fn rc_blake2b_new() -> *mut Blake2bVarCore {
    let core = Blake2bVarCore::new(64).expect("output size 64");
    Box::into_raw(Box::new(core))
}

/// One block through the RustCrypto core.
///
/// # Safety
/// `st` comes from `rc_blake2b_new`; `blk` points to 128 readable bytes.
#[no_mangle]
pub unsafe extern "C" fn rc_blake2b_update_block(st: *mut Blake2bVarCore, blk: *const u8) {
    let block: &Block<Blake2bVarCore> = &*(blk as *const Block<Blake2bVarCore>);
    (*st).update_blocks(core::slice::from_ref(block));
}

/// BLAKE2b-512 of `msg[0..len)` by RustCrypto `Blake2b512`, into `out[0..64)`.
///
/// # Safety
/// `msg` points to `len` readable bytes, `out` to 64 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn rc_blake2b512(msg: *const u8, len: usize, out: *mut u8) {
    let d = Blake2b512::digest(core::slice::from_raw_parts(msg, len));
    core::ptr::copy_nonoverlapping(d.as_ptr(), out, 64);
}

/// The libcrux streaming state with a 64-byte digest, behind its `update`. The crate does not
/// export the type parameter of its state, so the state is captured by a closure, and each
/// call of the arm is one indirect call more than a direct `update`.
pub type LcUpdate = Box<dyn FnMut(&[u8])>;

/// A fresh libcrux BLAKE2b state with a 64-byte digest.
#[no_mangle]
pub extern "C" fn lc_blake2b_new() -> *mut LcUpdate {
    let mut st = Blake2bBuilder::new_unkeyed()
        .build_const_digest_len::<64>()
        .expect("digest length 64");
    let upd: LcUpdate = Box::new(move |chunk: &[u8]| {
        let _ = st.update(chunk);
    });
    Box::into_raw(Box::new(upd))
}

/// One 128-byte `update` of the libcrux state.
///
/// # Safety
/// `st` comes from `lc_blake2b_new`; `blk` points to 128 readable bytes.
#[no_mangle]
pub unsafe extern "C" fn lc_blake2b_update_block(st: *mut LcUpdate, blk: *const u8) {
    (*st)(core::slice::from_raw_parts(blk, 128));
}

/// BLAKE2b-512 of `msg[0..len)` by libcrux, into `out[0..64)`.
///
/// # Safety
/// `msg` points to `len` readable bytes, `out` to 64 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn lc_blake2b512(msg: *const u8, len: usize, out: *mut u8) {
    let mut st = Blake2bBuilder::new_unkeyed()
        .build_const_digest_len::<64>()
        .expect("digest length 64");
    let _ = st.update(core::slice::from_raw_parts(msg, len));
    let mut d = [0u8; 64];
    st.finalize(&mut d);
    core::ptr::copy_nonoverlapping(d.as_ptr(), out, 64);
}
