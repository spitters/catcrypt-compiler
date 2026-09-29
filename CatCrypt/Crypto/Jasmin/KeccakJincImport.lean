/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCrypt.Crypto.Jasmin.JincInline
public import CatCrypt.Crypto.Jasmin.JincElab

/-!
# Keccak-f[1600] from the formosa-keccak Jasmin source

The scalar Keccak-f[1600] permutation of formosa-crypto's `formosa-keccak`
(the Keccak code libjade builds on), taken through the `.jinc` importer and the
owned x86 backend. No jasminc: the Jasmin text is the input of the front.

Source: https://github.com/formosa-crypto/formosa-keccak at commit
`fe5d22fa85672ffbe5cfb4845037b50cf2eaa1f7` (licence CC0-1.0 OR Apache-2.0). The
three units below are the files `src/amd64/common/keccakf1600_generic.jinc`,
`src/amd64/ref/select_bmi1.jinc` and `src/amd64/ref/keccakf1600.jinc` of that
commit, verbatim except for trailing whitespace. `keccakWrapperSrc` is the entry point written for this import:
`keccak_f1600(out, inp)` copies the 25 lanes of `inp` to `out` and runs
`_keccakf1600_ref` on `out`, the two-pointer ABI of the other owned Keccak kernels
(`uint64_t *keccak_f1600(uint64_t *out, const uint64_t *inp)`, `out` in `%rdi`).
The copy is a load and a store per lane in source order, so `out = inp` is a valid
call.

`JincInline.importFun` inlines every call, folds the round counter, the rotation
offsets and the round constants, and keeps the 5-lane `reg` arrays and the
`stack` state `s_e` as one value per cell. The `reg ptr` state is memory: each
round pair reads it with `load`s and writes it with `store`s. `JincElab.elabFun`
elaborates the result to a `Com jasminDialect`, and `JincElab.emitJFunAsm`
renders it through `Com.toLprogPhysAbi` and `renderOwned`.

`JincInline.importFunRolled` keeps the round loop rolled instead: one trip is a
round pair, the round counter is `2·idx` at the trip index `idx`, and the round
constants are read from the `.rodata` table `KECCAK1600_RC`.
`JincElab.emitJFunRolledAsm` renders it as a counted loop.

The sponges SHA3-256, SHAKE128 and SHAKE256 are imported from the sponge files
of the same commit with entry points written for the import (`keccakSpongeUnit`):
the input and output lengths are run-time values, each full block is absorbed or
squeezed in a run-time loop around a call of the permutation `_keccakf1600_ref`,
and the partial block byte by byte. `keccakSpongeAsm` renders the three sponges
and the permutation as one program (`JincElab.emitRolledProgramAsm`).

The four-way permutation `_keccakf1600_avx2x4` is imported from the AVX2 files
of the same commit (`keccakX4Unit`), its round loop kept rolled: the state is
four Keccak states in struct-of-arrays order, lane `i` of all four the 256-bit
cell `i`, and every operation is a 256-bit op (`Rhs.ymm`). The round constants
are loads from the table `KECCAK1600_RC_bcast4u64`, each constant in all four
lanes, and the byte-shuffle masks `ROL8` and `ROL56` are one-cell `.rodata`
tables. `keccakF1600X4RolledAsm` renders it under the ABI of the owned
`keccak_f1600_x4(uint64_t *out, const uint64_t *in)`.

The executable `keccak-jinc-emit` (`KeccakJincEmit.lean`) writes the renderings;
the bench harness `bench/keccak_compare` checks them against FIPS 202.

## Main definitions

* `keccakUnit`: the concatenated source unit.
* `keccakF1600JFun`: the imported straight-line `JFun` of `keccak_f1600`.
* `keccakF1600Asm`: its owned AT&T rendering.
* `keccakF1600Rolled`, `keccakF1600RolledAsm`: the import with the round loop
  kept rolled, and its owned AT&T rendering.
* `keccakSpongeUnit`, `keccakSpongeImports`, `keccakSpongeAsm`: the sponge source
  unit, its imported entry points and permutation, and their owned AT&T
  rendering.
* `keccakX4Unit`, `keccakF1600X4Rolled`, `keccakF1600X4RolledAsm`: the four-way
  source unit, its import with the round loop kept rolled, and its owned AT&T
  rendering.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Jasmin.KeccakJincImport

open CatCrypt.Crypto.Jasmin.JincToCom (JFun)

/-- `src/amd64/common/keccakf1600_generic.jinc`: the round count, the round
    constants and the rotation offsets. -/
def keccakGenericSrc : String := r#"param int KECCAK_ROUNDS = 24;

u64[24] KECCAK1600_RC =
{  0x0000000000000001
  ,0x0000000000008082
  ,0x800000000000808a
  ,0x8000000080008000
  ,0x000000000000808b
  ,0x0000000080000001
  ,0x8000000080008081
  ,0x8000000000008009
  ,0x000000000000008a
  ,0x0000000000000088
  ,0x0000000080008009
  ,0x000000008000000a
  ,0x000000008000808b
  ,0x800000000000008b
  ,0x8000000000008089
  ,0x8000000000008003
  ,0x8000000000008002
  ,0x8000000000000080
  ,0x000000000000800a
  ,0x800000008000000a
  ,0x8000000080008081
  ,0x8000000000008080
  ,0x0000000080000001
  ,0x8000000080008008
};

inline fn keccakf1600_index(inline int x y) -> inline int
{
  inline int r;
  r = (x % 5) + 5 * (y % 5);
  return r;
}


inline fn keccakf1600_rho_offsets(inline int i) -> inline int
{
  inline int r x y z t;

  r = 0;
  x = 1;
  y = 0;

  for t = 0 to 24
  { if (i == x + 5 * y)
    { r = ((t + 1) * (t + 2) / 2) % 64; }
    z = (2 * x + 3 * y) % 5;
    x = y;
    y = z;
  }

  return r;
}

inline fn keccakf1600_rhotates(inline int x y) -> inline int
{
  inline int i r;
  i = keccakf1600_index(x, y);
  r = keccakf1600_rho_offsets(i);
  return r;
}
"#

/-- `src/amd64/ref/select_bmi1.jinc`: `__ANDN_64` as `!a & b`. -/
def keccakSelectBmi1Src : String := r#"inline fn __ANDN_64(reg u64 a b) -> reg u64 {
 reg u64 t;
 t = !a & b;
 return t;
}
"#

/-- `src/amd64/ref/keccakf1600.jinc`: the scalar permutation. -/
def keccakRefSrc : String := r#"/****************************************************************************

   DEPENDENCIES:
   =============

  The loading of this file depends on the following context:

 1) "select_nobmi1.jinc" or "select_bmi1.jinc"

*****************************************************************************/

from Keccak require "common/keccakf1600_generic.jinc"

inline fn __rol_u64_ref
( reg u64 x
, inline int i
) -> reg u64
{
  if (i != 0) {
    _, _, x = #ROL_64(x, i);
  }
  return x;
}


// C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]
inline fn __theta_sum_ref
( reg ptr u64[25] a
) -> reg u64[5]
{
  inline int x y;
  reg u64[5] c;

  // C[x] = A[x, 0]
  for x=0 to 5
  { c[x] = a[x + 0]; }

  // C[x] ^= A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]
  for y=1 to 5
  { for x=0 to 5
    { c[x] ^= a[x + y*5]; }
  }

  return c;
}

// D[x] = C[x-1] ^ ROT(C[x+1], 1)
inline fn __theta_rol_ref
( reg u64[5] c
) -> reg u64[5]
{
  inline int x;
  reg u64[5] d;

  for x = 0 to 5
  { // D[x] = C[x + 1]
    d[x] = c[(x + 1) % 5];

    // D[x] = ROT(D[x], 1)
    d[x] = __rol_u64_ref(d[x], 1);

    // D[x] ^= C[x-1]
    d[x] ^= c[(x - 1 + 5) % 5];
  }

  return d;
}

// B[x] = ROT( (A[x',y'] ^ D[x']), r[x',y'] ) with (x',y') = M^-1 (x,y)
//
// M = (0 1)  M^-1 = (1 3)  x' = 1x + 3y
//     (2 3)         (1 0)  y' = 1x + 0y
//
inline fn __rol_sum_ref
( reg ptr u64[25] a
, reg u64[5] d
, inline int y
) -> reg u64[5]
{
  inline int r x x_ y_;
  reg u64[5] b;

  for x = 0 to 5
  {
    x_ = (x + 3*y) % 5;
    y_ = x;
    r = keccakf1600_rhotates(x_, y_);

    // B[x] = A[x',y']
    b[x] = a[x_ + y_*5];

    // B[x] ^= D[x'];
    b[x] ^= d[x_];

    // B[x] = ROT( B[x], r[x',y'] );
    b[x] = __rol_u64_ref(b[x], r);

  }

  return b;
}


// E[x, y] = B[x] ^ ( (!B[x+1]) & B[x+2] )
// -- when x and y are 0: E[0,0] ^= RC[i];
#[safety =
   { requires = is_arr_init(b,0,40) && 0 <= y && y < 5 && is_arr_init(e,0,y*5*8)
   , ensures = is_arr_init(e,0,(y+1)*5*8) }
]
inline fn __set_row_ref
( reg ptr u64[25] e
, reg u64[5] b
, inline int y
/*, stack u64 s_rc*/
) -> reg ptr u64[25]
{
  inline int x x1 x2;
  reg u64 t;

  for x=0 to 5
  {
    x1 = (x + 1) % 5;
    x2 = (x + 2) % 5;

    t  = __ANDN_64(b[x1], b[x2]); //!b[x1] & b[x2];

    t ^= b[x];
    // if( x==0 && y==0 ){ t ^= s_rc; }
    e[x + y*5] = t;
  }

  return e;
}

#[safety =
   { requires = is_arr_init(a,0,200)
   , ensures = is_arr_init(e,0,200) }
]
fn _pround_ref
( reg ptr u64[25] e a
//, reg u64 rc
) -> reg ptr u64[25]
{
  inline int y;
  reg u64[5] b c d;

  c = __theta_sum_ref(a);
  d = __theta_rol_ref(c);

  for y = 0 to 5
  { b = __rol_sum_ref(a, d, y);
    e = __set_row_ref(e, b, y);
  }

  return e;
}

inline fn __keccakf1600_ref
( reg ptr u64[25] a
) -> reg ptr u64[25]
{
  reg ptr u64[24] RC;
  stack u64[25] s_e;
  reg ptr u64[25] e;
  reg ui64 c;
  reg u64 rc;

  e = s_e;

  c = 0;
  while
  {
    () = #spill(c);
    e = _pround_ref(e, a);
    a, e = #swap(e, a);
    RC = KECCAK1600_RC;
    rc = RC[c];
    e[0] ^= rc;

    a = _pround_ref(a, e);
    a, e = #swap(e, a);
    RC = KECCAK1600_RC;
    rc = RC[c+1];
    a[0] ^= rc;
    () = #unspill(c);
    c += 2;
  } (c < KECCAK_ROUNDS - 1)

  return a;
}


fn _keccakf1600_ref
( reg ptr u64[25] a
) -> reg ptr u64[25]
{
  a = __keccakf1600_ref(a);
  return a;
}


inline fn _keccakf1600_ref_
( reg ptr u64[25] a
) -> reg ptr u64[25]
{
  a = a;
  a = _keccakf1600_ref(a);
  a = a;
  return a;
}



/* For testing:
export fn test_keccakf1600_ref
( reg mut ptr u64[25] st
) -> reg ptr u64[25]
{
 st = _keccakf1600_ref_(st);
 return st;
}
*/
"#

/-- The entry point of the import: `out` receives the 25 lanes of `inp`, then the
    permutation in place. -/
def keccakWrapperSrc : String := r#"export fn keccak_f1600(reg ptr u64[25] out inp) -> reg ptr u64[25]
{
  inline int i;
  reg u64 t;
  for i = 0 to 25 { t = inp[i]; out[i] = t; }
  out = _keccakf1600_ref(out);
  return out;
}
"#

/-- The source unit: the generic constants, the BMI1 `__ANDN_64`, the scalar
    permutation and the entry point, in dependency order. -/
def keccakUnit : String :=
  keccakGenericSrc ++ keccakSelectBmi1Src ++ keccakRefSrc ++ keccakWrapperSrc

/-- The exported symbol. -/
def keccakF1600Sym : String := "keccak_f1600"

/-- The imported straight-line `JFun` of `keccak_f1600`. -/
def keccakF1600JFun : Except String JFun :=
  JincInline.importFun keccakUnit keccakF1600Sym

/-- The owned AT&T rendering of `keccak_f1600`, or the import error as an
    assembler comment. -/
def keccakF1600Asm : String :=
  match keccakF1600JFun with
  | .ok f => JincElab.emitJFunAsm f keccakF1600Sym
  | .error e => s!"; import error: {e}"

/-- `keccak_f1600` imported with its round loop kept rolled: the twelve trips of
    the `while`, two rounds each, are one `for` over the trip index, and the round
    constants are loads from the `.rodata` table `KECCAK1600_RC` at the indices
    `2·idx` and `2·idx + 1`. -/
def keccakF1600Rolled : Except String JincInline.RolledImport :=
  JincInline.importFunRolled keccakUnit keccakF1600Sym

/-- The owned AT&T rendering of `keccakF1600Rolled` (`JincElab.emitJFunRolledAsm`),
    or the import error as an assembler comment. -/
def keccakF1600RolledAsm : String :=
  match keccakF1600Rolled with
  | .ok r => JincElab.emitJFunRolledAsm r.fn r.tables keccakF1600Sym
  | .error e => s!"; import error: {e}"

/-! ## The sponges

The sponge sources of the same commit: `src/amd64/common/keccak1600_generic.jinc`,
`src/amd64/ref/keccak1600.jinc`, `src/amd64/common/subreadwrite_imem.jinc` and
`src/amd64/ref/keccak1600_fixedsizes.jinc`, verbatim except for trailing
whitespace. `keccakSpongeWrapperSrc` holds the entry points written for this
import. -/

/-- `src/amd64/common/keccak1600_generic.jinc`: the rates, the domain bytes, the
    state type and the shift helpers. -/
def keccakSpongeGenericSrc : String := r#"param int R72 = 72;
param int R104 = 104;
param int R136 = 136;
param int R144 = 144;
param int R168 = 168;

param int UNFINISHED = 0;
param int SHA3 = 0x06;
param int RAWSHAKE = 0x07;
param int SHAKE = 0x1F;

type keccak_state = u64[25];


/* UTILITY FUNCTIONS */

inline fn __SHLQ
( reg u64 x
, inline int shbytes
) -> reg u64
{
  if (shbytes != 0) {
    x <<= (8*shbytes);
  }
  return x;
}

inline fn __SHLDQ
( reg u128 x
, inline int shbytes
) -> reg u128
{
  if (shbytes != 0) {
    x = #VPSLLDQ_128(x, shbytes);
  }
  return x;
}

inline fn __SHLQ_256
( reg u256 x
, inline int shbytes
) -> reg u256
{
  if (shbytes != 0) {
    x = #VPSLL_4u64(x, 8*shbytes);
  }
  return x;
}
"#

/-- `src/amd64/ref/keccak1600.jinc`: the state initialisation and the final rate
    bit. -/
def keccakSpongeRefSrc : String := r#"/****************************************************************************

   DEPENDENCIES:
   =============

  The loading of this file depends on the following context:

 1) "select_nobmi1.jinc" or "select_bmi1.jinc"

*****************************************************************************/

require "keccakf1600.jinc"

/*
   STATE INIT
   ==========
*/
#[safety =
   { ensures = is_arr_init(st,0,200) }
]
inline fn __state_init_ref
( reg mut ptr u64[25] st
) -> reg ptr u64[25]
{
  reg ui64 i;
  reg u64 z64;
  z64 = 0;
  i = 0;
  while (i < 25) {
    st[(uint) i] = z64;
    i += 1;
  }
  return st;
}

/*
   ADD RATE BIT
   ============
*/
#[safety =
   { requires = is_arr_init(st,0,200) && 0 < _RATE8 && _RATE8 <= 200
   , ensures = is_arr_init(st,0,200) }
]
inline fn __addratebit_ref
( reg mut ptr u64[25] st
, inline int _RATE8
) -> reg ptr u64[25]
{
/*  reg u64 t64;
  t64 = 1;
  t64 <<= (8*_RATE8-1) % 64; // obs: should be 63 for all admissible rates!
  t64 ^= st[(_RATE8-1)/8];
  st[(_RATE8-1)/8] = t64;
*/
  st.[:u8 _RATE8-1] ^= 0x80;
  return st;
}
"#

/-- `src/amd64/common/subreadwrite_imem.jinc`: reads and writes of up to 8, 16
    and 32 bytes of memory. -/
def keccakSubReadWriteSrc : String := r#"require "keccak1600_generic.jinc"

/*
 *  REMARK: this file is expected to be kept in sync. with the array version's
 *  counterpart ("subreadwrite_ASIZE.jinc")
 *
 */



/**
    READ A FIXED NUMBER OF BYTES FROM MEMORY INTO A WORD
**/
#[safety =
   { requires = is_mem_init((64u) buf,max(LEN,8 - (AT-CUR))) && 0<=LEN
     && 0 <= TRAIL && TRAIL < 256
   , res = { final_buf, final_LEN, final_TRAIL, final_AT, final_w }
   , ensures =  (CUR <= AT && AT < CUR + 8) ?
       ( final_buf == buf + max(0,min(LEN,8 - (AT-CUR)))
     && final_LEN == LEN - max(0,min(LEN,8- (AT-CUR)))
     && final_TRAIL == (8 <=s AT-CUR + LEN ? TRAIL : 0)
     && final_AT == CUR + max(0,min(AT-CUR + LEN,8) + (8 <=s AT-CUR + LEN || TRAIL==0 ? 0 : 1)))
     : (final_buf == buf
      && final_LEN == LEN
      && final_TRAIL == TRAIL
      && final_AT == AT)
   }
 ]
inline fn __m_ilen_read_upto8_at
( reg ui64 buf
, inline int LEN
, inline int TRAIL
, inline int CUR
, inline int AT
) -> reg ui64   /* buf */
   , inline int /* LEN */
   , inline int /* TRAIL */
   , inline int /* AT */
   , reg u64    /* w */
{
  reg u64 w, t16, t8;
  inline int AT8;

  if ( AT < CUR || CUR+8 <= AT || LEN==0 && TRAIL==0 ) { // nothing to be done...
    w = 0;
  } else {
    AT8 = AT-CUR;
    if (8 <= LEN) {
      w = [:u64 (64u) buf];
      w = __SHLQ(w, AT8);
      buf += 8-AT8;
      LEN -= 8-AT8;
      AT8 = 8;
    } else {
      if (4 <= LEN) {
	w = (64u) [:u32 (64u) buf];
	w = __SHLQ(w, AT8);
	buf += (4+AT8 >= 8 ? 8-AT8 : 4);
	LEN -= (4+AT8 >= 8 ? 8-AT8 : 4);
	AT8 = (4+AT8 >= 8 ? 8 : 4+AT8); // AT8==8: finished!
      } else {
	w = 0;
      }
      if (AT8 < 8 && 2 <= LEN) {
	t16 = (64u) [:u16 (64u) buf];
	buf += (2+AT8 >= 8 ? 8-AT8 : 2);
	LEN -= (2+AT8 >= 8 ? 8-AT8 : 2);
	t16 = __SHLQ(t16, AT8);
	w |= t16;
	AT8 = (2+AT8 >= 8 ? 8 : 2+AT8);
      }
      if (AT8 < 8) {
	if ( 1 <= LEN ) {
	  t8 = (64u) [:u8 (64u) buf];
	  t8 |= 256*(TRAIL%256);
	  buf += 1;
	  LEN -= 1;
	  t8 = __SHLQ(t8, AT8);
	  w |= t8;
	  AT8 += 1;
	  if (AT8 < 8 && TRAIL%256 != 0) {
	    AT8 += 1;
	    TRAIL = 0;
	  }
	} else if ( TRAIL%256 != 0) {
	  t8 = TRAIL%256;
	  t8 = __SHLQ(t8, AT8);
	  w |= t8;
	  TRAIL = 0;
	  AT8 += 1;
	}
      }
    }
    AT = CUR + AT8;
  }
  return buf, LEN, TRAIL, AT, w;
}

#[safety =
   { requires = is_mem_init((64u) buf,max(LEN,16 - (AT-CUR))) && 0<=LEN
     && 0 <= TRAIL && TRAIL < 256
    , res = { final_buf, final_LEN, final_TRAIL, final_AT, final_w }
    , ensures =  (CUR <= AT && AT < CUR + 16) ?
       ( final_buf == buf + max(0,min(LEN,16 - (AT-CUR)))
     && final_LEN == LEN - max(0,min(LEN,16- (AT-CUR)))
     && final_TRAIL == (16 <=s AT-CUR + LEN ? TRAIL : 0)
     && final_AT == CUR + max(0,min(AT-CUR + LEN,16) + (16 <=s AT-CUR + LEN || TRAIL==0 ? 0 : 1)))
     : (final_buf == buf
      && final_LEN == LEN
      && final_TRAIL == TRAIL
      && final_AT == AT)
   }
 ]
inline fn __m_ilen_read_upto16_at
( reg ui64 buf
, inline int LEN
, inline int TRAIL
, inline int CUR
, inline int AT
) -> reg ui64   /* buf */
   , inline int /* LEN */
   , inline int /* TRAIL */
   , inline int /* AT */
   , reg u128    /* w */
{
  reg u64 t64_0, t64_1;
  reg u128 w;
  inline int AT16;

  if ( AT < CUR || CUR+16 <= AT || LEN==0 && TRAIL==0 ) { // nothing to be done...
    w = #set0_128();
  } else {
    AT16 = AT-CUR;
    if ( 16 <= LEN ) {
      w = [:u128 (64u) buf];
      w = __SHLDQ(w, AT16);
      buf += 16-AT16;
      LEN -= 16-AT16;
      AT16 = 16;
    } else if ( 8 <= AT16 ) {
      w = #set0_128();
      buf, LEN, TRAIL, AT16, t64_1 = __m_ilen_read_upto8_at(buf, LEN, TRAIL, 8, AT16);
      w = #VPINSR_2u64(w, t64_1, 1);
    } else {
      buf, LEN, TRAIL, AT16, t64_0 = __m_ilen_read_upto8_at(buf, LEN, TRAIL, 0, AT16);
      w = (128u) t64_0;
      buf, LEN, TRAIL, AT16, t64_1 = __m_ilen_read_upto8_at(buf, LEN, TRAIL, 8, AT16);
      w = #VPINSR_2u64(w, t64_1, 1);
    }
    AT = CUR+AT16;
  }
  return buf, LEN, TRAIL, AT, w;
}

#[safety =
   { requires = is_mem_init((64u) buf,max(LEN,32 - (AT-CUR))) && 0<=LEN
     && 0 <= TRAIL && TRAIL < 256
   , res = { final_buf, final_LEN, final_TRAIL, final_AT, final_w }
   , ensures =  (CUR <= AT && AT < CUR + 32) ?
       ( final_buf == buf + max(0,min(LEN,32 - (AT-CUR)))
     && final_LEN == LEN - max(0,min(LEN,32- (AT-CUR)))
     && final_TRAIL == (32 <=s AT-CUR + LEN ? TRAIL : 0)
     && final_AT == CUR + max(0,min(AT-CUR + LEN,32) + (32 <=s AT-CUR + LEN || TRAIL==0 ? 0 : 1)))
     : (final_buf == buf
      && final_LEN == LEN
      && final_TRAIL == TRAIL
      && final_AT == AT)
   }
 ]
inline fn __m_ilen_read_upto32_at
( reg ui64 buf
, inline int LEN
, inline int TRAIL
, inline int CUR
, inline int AT
) -> reg ui64   /* buf */
   , inline int /* LEN */
   , inline int /* TRAIL */
   , inline int /* AT */
   , reg u256    /* w */
{
  reg u128 t128_0, t128_1;
  reg u256 w;
  inline int AT32;

  if ( AT < CUR || CUR+32 <= AT || LEN==0 && TRAIL==0) { // nothing to be done...
    w = #set0_256();
  } else {
    AT32 = AT-CUR;
    if ( AT32==0 && 32 <= LEN ) {
      w = [:u256 (64u) buf];
      AT32 += 32;
      buf += 32;
      LEN -= 32;
    } else if ( 16 <= AT32 ) {
      w = #set0_256();
      buf, LEN, TRAIL, AT32, t128_1 = __m_ilen_read_upto16_at(buf, LEN, TRAIL, 16, AT32);
      w = #VINSERTI128(w, t128_1, 1);
    } else {
      buf, LEN, TRAIL, AT32, t128_0 = __m_ilen_read_upto16_at(buf, LEN, TRAIL,  0, AT32);
      buf, LEN, TRAIL, AT32, t128_1 = __m_ilen_read_upto16_at(buf, LEN, TRAIL, 16, AT32);
      w = (2u128)[t128_1, t128_0];
    }
    AT = CUR+AT32;
  }
  return buf, LEN, TRAIL, AT, w;
}

#[safety =
   { requires = is_mem_init((64u) buf,max(LEN,8 - (AT-CUR))) && 0<=LEN
     && 0 <= TRAIL && TRAIL < 256
   , res = { final_buf, final_LEN, final_TRAIL, final_AT, final_w }
   , ensures =  (CUR <= AT && AT < CUR + 8) ?
       ( final_buf == buf + max(0,min(LEN,8 - (AT-CUR)))
     && final_LEN == LEN - max(0,min(LEN,8- (AT-CUR)))
     && final_TRAIL == (8 <=s AT-CUR + LEN ? TRAIL : 0)
     && final_AT == CUR + max(0,min(AT-CUR + LEN,8) + (8 <=s AT-CUR + LEN || TRAIL==0 ? 0 : 1)))
     : (final_buf == buf
      && final_LEN == LEN
      && final_TRAIL == TRAIL
      && final_AT == AT)
   }
 ]
inline fn __m_ilen_read_bcast_upto8_at
( reg ui64 buf
, inline int LEN
, inline int TRAIL
, inline int CUR
, inline int AT
) -> reg ui64   /* buf */
   , inline int /* LEN */
   , inline int /* TRAIL */
   , inline int /* AT */
   , reg u256   /* w */
{
  reg u64 w;
  reg u128 t128;
  reg u256 w256;
  inline int AT8;

  if ( AT < CUR || CUR+8 <= AT || LEN==0 && TRAIL==0 ) { // nothing to be done...
    w256 = #set0_256();
  } else {
    if (8 <= LEN) {
      AT8 = AT-CUR;
      w256 = #VPBROADCAST_4u64([:u64 (64u) buf]);
      w256 = __SHLQ_256(w256, AT8);
      buf += 8-AT8;
      LEN -= 8-AT8;
      AT = CUR + 8;
    } else {
      AT8 = AT-CUR;
      buf, LEN, TRAIL, AT, w = __m_ilen_read_upto8_at(buf, LEN, TRAIL, CUR, AT);
      t128 = (128u) w;
      w256 = #VPBROADCAST_4u64(t128);
      w256 = __SHLQ_256(w256, AT8);
    }
  }
  return buf, LEN, TRAIL, AT, w256;
}

/**
    WRITE A FIXED NUMBER OF BYTES FROM MEMORY INTO A WORD
**/

// __awrite_subu64
#[safety =
   { requires = is_mem_init((64u) buf,min(LEN,8))
   , res = { final_buf, final_LEN}
   , ensures = final_buf == buf + max(0,min(LEN,8))
     && final_LEN == LEN - max(0,min(LEN,8))
   }
 ]
inline fn __m_ilen_write_upto8
( reg ui64 buf
, inline int LEN
, reg u64 w
) -> reg ui64 /* buf */
   , inline int /* LEN */
{
  if (0 < LEN) {
    if (8 <=s LEN) {
      [:u64 (64u) buf] = w;
      buf += 8;
      LEN -= 8;
    } else {
      if (4 <=s LEN) {
        [:u32 (64u) buf] = (32u) w;
	w >>= 32;
        buf += 4;
        LEN -= 4;
      }
      if (2 <=s LEN) {
        [:u16 (64u) buf] = (16u) w;
	w >>= 16;
        buf += 2;
        LEN -= 2;
      }
      if (1 <=s LEN) {
        [:u8 (64u) buf] = (8u) w;
        buf += 1;
        LEN -= 1;
      }
    }
  }
  return buf, LEN;
}

// __awrite_subu128
#[safety =
   { requires = is_mem_init((64u) buf,min(LEN,16))
   , res = { final_buf, final_LEN}
   , ensures = final_buf == buf + max(0,min(LEN,16))
     && final_LEN == LEN - max(0,min(LEN,16))
   }
 ]
inline fn __m_ilen_write_upto16
( reg ui64 buf
, inline int LEN
, reg u128 w
) -> reg ui64     /* buf */
   , inline int   /* LEN */
{
  reg u64 t64;
  if (0 < LEN) {
    if (16 <=s LEN) {
      [:u128 (64u) buf] = w;
      buf += 16;
      LEN -= 16;
    } else {
      if (8 <=s LEN) {
        [:u64 (64u) buf] = #MOVV(w);
        buf += 8;
        LEN -= 8;
        w = #VPUNPCKH_2u64(w, w);
      }
      t64 = (64u) w;
      buf, LEN = __m_ilen_write_upto8(buf, LEN, t64);
    }
  }
  return buf, LEN;
}

// __awrite_subu256
#[safety =
   { requires = is_mem_init((64u) buf,min(LEN,32))
   , res = { final_buf, final_LEN}
   , ensures = final_buf == buf + max(0,min(LEN,32))
     && final_LEN == LEN - max(0,min(LEN,32))
   }
 ]
inline fn __m_ilen_write_upto32
( reg ui64 buf
, inline int LEN
, reg u256 w
) -> reg ui64   /* buf */
   , inline int /* LEN */
{
  reg u128 t128;
  if (0 < LEN) {
    if (32 <= LEN) {
      [:u256 (64u) buf] = w;
      buf += 32;
      LEN -= 32;
    } else {
      t128 = (128u) w;
      if (16 <= LEN) {
        [:u128 (64u) buf] = t128;
        buf += 16;
        LEN -= 16;
        t128 = #VEXTRACTI128(w, 1);
      }
      buf, LEN = __m_ilen_write_upto16(buf, LEN, t128);
    }
  }
  return buf, LEN;
}


/**
    READ A VARIABLE NUMBER OF BYTES FROM MEMORY INTO A WORD
**/
#[safety =
   { requires = is_mem_init((64u) buf,min(len,8))
   , res = { final_buf, final_data}
   , ensures = final_buf == buf + min(len,8)
   }
 ]
inline fn __m_rlen_read_upto8
( reg ui64 buf
, reg ui64 len // off + len <= ASIZE
) -> reg ui64 /* buf */
   , reg u64  /* data */
{
  reg u64 w, x;
  reg u8 sh;
  reg bool zf;

  if (len >= 8) {
    w = [:u64 (64u) buf];
    buf += 8;
  } else {
    _, _, _, _, zf = #TEST((64u)len, 4);
    if (!zf) {
      w = (64u) [:u32 (64u) buf];
      buf += 4;
      sh = 32;
    } else {
      w = 0;
      sh = 0;
    }
    _, _, _, _, zf = #TEST((64u)len, 2);
    if (!zf) {
      x = (64u) [:u16 (64u) buf];
      x <<= (sh & 63);
      w += x;
      buf += 2;
      sh += 16;
    }
    _, _, _, _, zf = #TEST((64u)len, 1);
    if (!zf) {
      x = (64u) [:u8 (64u) buf];
      x <<= (sh & 63);
      w += x;
      buf += 1;
    }
  }
  return buf, w;
}


/**
    WRITE A VARIABLE NUMBER OF BYTES FROM AN ARRAY INTO A WORD
**/
#[safety =
   { requires = is_mem_init((64u) buf,min(len,8))
   , res = { final_buf}
   , ensures = final_buf == buf + max(0,min(len,8))
   }
 ]
inline fn __m_rlen_write_upto8
( reg ui64 buf
, reg u64 data
, reg ui64 len // off + len <= ASIZE
) -> reg ui64   /* buf */
{
  reg bool zf;

  if (len >= 8) {
    [:u64 (64u) buf] = data;
    buf += 8;
  } else {
    _, _, _, _, zf = #TEST((64u)len, 4);
    if (!zf) {
      [:u32 (64u) buf] = (32u) data;
      buf += 4;
      data >>= 32;
    }
    _, _, _, _, zf = #TEST((64u)len, 2);
    if (!zf) {
      [:u16 (64u) buf] = (16u) data;
      buf += 2;
      data >>= 16;
    }
    _, _, _, _, zf = #TEST((64u)len, 1);
    if (!zf) {
      [:u8 (64u) buf] = (8u) data;
      buf += 1;
    }
  }
  return buf;
}
"#

/-- `src/amd64/ref/keccak1600_fixedsizes.jinc`: the absorb and squeeze of a
    compile-time number of bytes through memory. -/
def keccakFixedSizesSrc : String := r#"/****************************************************************************

   DEPENDENCIES:
   =============

  The loading of this file depends on the following context:

 1) "select_nobmi1.jinc" or "select_bmi1.jinc"

*****************************************************************************/

require "keccak1600.jinc"
from Keccak require "common/subreadwrite_imem.jinc"


/*
 *  REMARK: the remaining of this file is expected to be kept in sync. with its array version's
 *  counterpart ("keccak1600_fixedsizes_ASIZE.jinc")
 *
 */


/*
   INCREMENTAL ARRAY ABSORB
   ========================
*/
#[safety =
   { requires = 0 <= _TRAILB && _TRAILB < 256 && 0<=_LEN && _LEN <= 200 && is_mem_init((64u) buf,_LEN) && is_arr_init(st,0,7*32) && 0<= AT && AT < 200
   , res = { final_st, final_AT, final_buf }
   , ensures = is_arr_init(final_st,0,7*32) && final_AT == AT + _LEN + (_TRAILB != 0 ? 1 : 0) && final_buf == buf + _LEN
   }
 ]
inline fn __addstate_m_ref
( reg mut ptr u64[25] st
, inline int AT /* bytes (0 <= AT < 200) */
, reg ui64 buf
, inline int _LEN
, inline int _TRAILB
) -> reg ptr u64[25] /* st */
   , inline int      /* AT */
   , reg ui64        /* buf */
{
  inline int AT8;
  reg ui64 at;
  reg u64 w;

  // fill first word...
  AT8 = AT;
  AT = 8*(AT/8);
  if ( AT8%8 != 0 ) {
    buf, _LEN, _TRAILB, AT8, w = __m_ilen_read_upto8_at(buf, _LEN, _TRAILB, AT, AT8);
    st[AT/8] ^= w;
    AT = AT8;
  }

  // add complete words
  at = AT/8;
  while ( at < AT/8 + _LEN/8 ) {
    w = [:u64 (64u) buf];
    buf += 8;
    st[at] ^= w;
    at += 1;
  }

  // add last word...
  AT += 8*(_LEN/8);
  _LEN = _LEN%8;
  if ( 0 < _LEN || _TRAILB%256!= 0 ) {
    buf, _LEN, _TRAILB, AT, w = __m_ilen_read_upto8_at(buf, _LEN, _TRAILB, AT, AT);
    st[at] ^= w;
  }

  return st, AT, buf;
}

#[safety =
   { requires = 0 <= _TRAILB && _TRAILB < 256 && 0<=_LEN && 0<_RATE8 && _RATE8< 200 &&
                is_mem_init((64u) buf,_LEN) && is_arr_init(st,0,7*32) && 0<= AT && AT < 200
   , res = { final_st, final_AT, final_buf }
   , ensures = is_arr_init(final_st,0,7*32) && final_AT == AT + _LEN + (_TRAILB != 0 ? 1 : 0)
   }
 ]
inline fn __absorb_m_ref
( reg mut ptr u64[25] st
, inline int AT
, reg ui64 buf
, inline int _LEN
, inline int _TRAILB /* closes state if !=0 (i.e. adds trailbyte and padding) */
, inline int _RATE8
) -> reg ptr u64[25] /* st */
   , inline int      /* AT */
   , reg ui64        /* buf */
{
  reg ui64 i;
  inline int ITERS;

  if ( AT+_LEN >= _RATE8 ) { // more than one block...
    st, _, buf = __addstate_m_ref(st, AT, buf, _RATE8-AT, 0);
    _LEN = _LEN - (_RATE8-AT);
    AT = 0;
    () = #spill(buf);
    st = _keccakf1600_ref(st);
    () = #unspill(buf);
    ITERS = _LEN/_RATE8;
    i = 0;
    while ( i < ITERS ) {
      st, _, buf = __addstate_m_ref(st, 0, buf, _RATE8, 0);
      () = #spill(buf,i);
      st = _keccakf1600_ref(st);
      () = #unspill(buf,i);
      i += 1;
    }
    _LEN = _LEN % _RATE8;
  }
  st, AT, buf = __addstate_m_ref(st, AT, buf, _LEN, _TRAILB);
  if (_TRAILB!=0) { st = __addratebit_ref(st, _RATE8); }

  return st, AT, buf;
}


/*
   ONE-SHOT (FIXED-SIZE) MEMORY SQUEEZE
   ====================================
*/
#[safety =
   { requires = 0<= _LEN && _LEN <= 200 && is_mem_init((64u) buf,_LEN) && is_arr_init(st,0,7*32)
   , res = { final_buf }
   , ensures = final_buf == buf + _LEN
   }
 ]
inline fn __dumpstate_m_ref
( reg ui64 buf
, inline int _LEN
, reg const ptr u64[25] st
) -> reg ui64     /* buf */
{
  reg ui64 i;
  reg u64 t;

  i = 0;
  while (i < _LEN/8) {
    t = st[i];
    [:u64 (64u) buf] = t;
    buf += 8;
    i += 1;
  }
  if (0 < _LEN%8) {
    t = st[i];
    buf, _ = __m_ilen_write_upto8( buf, _LEN%8, t);
  }

  return buf;
}

#[safety =
   { requires = 0<= _LEN && 0< _RATE8 && _RATE8 < 200 && is_mem_init((64u) buf,_LEN) && is_arr_init(st,0,32*7)
   , ensures = is_arr_init(st,0,32*7)
   }
 ]
inline fn __squeeze_m_ref
( reg mut ptr u64[25] st
, reg ui64 buf
, inline int _LEN
, inline int _RATE8
) -> reg ptr u64[25] /* st */
   , reg ui64        /* buf */
{
  reg ui64 i;

  i = 0;
  while (i < _LEN/_RATE8) {
    () = #spill(buf,i);
    st = _keccakf1600_ref(st);
    () = #unspill(buf,i);
    buf = __dumpstate_m_ref(buf, _RATE8, st);
    i += 1;
  }
  if (0 < _LEN%_RATE8) {
    () = #spill(buf);
    st = _keccakf1600_ref(st);
    () = #unspill(buf);
    buf = __dumpstate_m_ref(buf, _LEN%_RATE8, st);
  }

  return st, buf;
}
"#

/-- The entry points of the sponge import, written for it: `sha3_256_jinc(out,
    in, inlen)`, `shake128_jinc(out, outlen, in, inlen)` and
    `shake256_jinc(out, outlen, in, inlen)`, each returning `out`. The state is
    a `stack` array of the entry point's frame. `__absorb_rt` absorbs the
    `inlen / r` full blocks with `__addstate_m_ref` and a call of
    `_keccakf1600_ref` each, then the remaining bytes one at a time, the domain
    byte `TRAILB` and the rate bit (`__addratebit_ref`). `__squeeze_rt` writes the
    `outlen / r` full blocks with `__dumpstate_m_ref` after a permutation each,
    then permutes and writes the remaining bytes one at a time. SHA3-256 squeezes
    its 32 bytes with `__squeeze_m_ref`. -/
def keccakSpongeWrapperSrc : String := r#"
inline fn __absorb_rt
( reg ptr u64[25] st
, reg u64 in
, reg u64 inlen
, inline int TRAILB
, inline int RATE8
) -> reg ptr u64[25]
{
  reg u64 nblk i p rem j t;

  nblk = inlen / RATE8;
  rem = inlen % RATE8;
  t = nblk * RATE8;
  i = 0;
  while (i < nblk) {
    p = i * RATE8;
    p += in;
    st, _, _ = __addstate_m_ref(st, 0, p, RATE8, 0);
    st = _keccakf1600_ref(st);
    i += 1;
  }
  p = in + t;
  j = 0;
  while (j < rem) {
    t = (64u) [:u8 p + j];
    st.[:u8 j] ^= (8u) t;
    j += 1;
  }
  st.[:u8 rem] ^= TRAILB;
  st = __addratebit_ref(st, RATE8);
  return st;
}

inline fn __squeeze_rt
( reg ptr u64[25] st
, reg u64 out
, reg u64 outlen
, inline int RATE8
) -> reg ptr u64[25]
{
  reg u64 nblk i p rem j t;

  nblk = outlen / RATE8;
  rem = outlen % RATE8;
  t = nblk * RATE8;
  i = 0;
  while (i < nblk) {
    st = _keccakf1600_ref(st);
    p = i * RATE8;
    p += out;
    _ = __dumpstate_m_ref(p, RATE8, st);
    i += 1;
  }
  st = _keccakf1600_ref(st);
  p = out + t;
  j = 0;
  while (j < rem) {
    t = (64u) st.[:u8 j];
    [:u8 p + j] = (8u) t;
    j += 1;
  }
  return st;
}

export fn sha3_256_jinc(reg u64 out in inlen) -> reg u64
{
  stack u64[25] st_s;
  reg ptr u64[25] st;

  st = st_s;
  st = __state_init_ref(st);
  st = __absorb_rt(st, in, inlen, SHA3, R136);
  st, _ = __squeeze_m_ref(st, out, 32, R136);
  return out;
}

export fn sha3_512_jinc(reg u64 out in inlen) -> reg u64
{
  stack u64[25] st_s;
  reg ptr u64[25] st;

  st = st_s;
  st = __state_init_ref(st);
  st = __absorb_rt(st, in, inlen, SHA3, R72);
  st, _ = __squeeze_m_ref(st, out, 64, R72);
  return out;
}

export fn shake128_jinc(reg u64 out outlen in inlen) -> reg u64
{
  stack u64[25] st_s;
  reg ptr u64[25] st;

  st = st_s;
  st = __state_init_ref(st);
  st = __absorb_rt(st, in, inlen, SHAKE, R168);
  st = __squeeze_rt(st, out, outlen, R168);
  return out;
}

export fn shake256_jinc(reg u64 out outlen in inlen) -> reg u64
{
  stack u64[25] st_s;
  reg ptr u64[25] st;

  st = st_s;
  st = __state_init_ref(st);
  st = __absorb_rt(st, in, inlen, SHAKE, R136);
  st = __squeeze_rt(st, out, outlen, R136);
  return out;
}
"#

/-- The sponge source unit: the permutation units, the sponge units and the
    entry points, in dependency order. -/
def keccakSpongeUnit : String :=
  keccakGenericSrc ++ keccakSelectBmi1Src ++ keccakRefSrc ++ keccakSpongeGenericSrc
    ++ keccakSpongeRefSrc ++ keccakSubReadWriteSrc ++ keccakFixedSizesSrc
    ++ keccakSpongeWrapperSrc

/-- The permutation the sponges call, kept as a call to its own function. -/
def keccakSpongePermSym : String := "_keccakf1600_ref"

/-- The exported sponge symbols. -/
def keccakSpongeSyms : List String :=
  ["sha3_256_jinc", "sha3_512_jinc", "shake128_jinc", "shake256_jinc"]

/-- The sponges and the permutation they call, each imported with its loops kept
    rolled and every call of `keccakSpongePermSym` kept as a call. -/
def keccakSpongeImports : Except String (List (String × JincInline.RolledImport)) :=
  (keccakSpongeSyms ++ [keccakSpongePermSym]).mapM fun s =>
    (JincInline.importFunRolledWith [keccakSpongePermSym] keccakSpongeUnit s).map (s, ·)

/-- The owned AT&T rendering of the three sponges and the permutation as one
    program (`JincElab.emitRolledProgramAsm`), or the import error as an
    assembler comment. -/
def keccakSpongeAsm : String :=
  match keccakSpongeImports with
  | .ok rs =>
      let tables := rs.foldl (fun acc (_, r) =>
        acc ++ r.tables.filter (fun t => !acc.any (·.1 == t.1))) []
      JincElab.emitRolledProgramAsm (rs.map fun (s, r) => (r.fn, r.slots, s)) tables
  | .error e => s!"; import error: {e}"

/-! ## The four-way permutation

The AVX2 files `src/amd64/avx2/keccakf1600x4_pround_inlined.jinc` and
`src/amd64/avx2/keccakf1600x4.jinc` of the same commit, verbatim except for
trailing whitespace. `keccakX4WrapperSrc` holds the entry point written for this
import. -/

/-- `src/amd64/avx2/keccakf1600x4_pround_inlined.jinc`: one round of the four-way
    permutation without ι, over 256-bit lanes. -/
def keccakX4PRoundSrc : String := r#"/* -------------------------------------------------------------------- */
/* After add assignments before and after call to ensure that arguments and results are "reg ptr" */

#[safety =
   { requires = is_arr_init(a,0,800)
   , ensures = is_arr_init(e,0,800)
   }
 ]
fn _keccakf1600_4x_pround
( reg mut ptr u256[25] e
, reg const ptr u256[25] a
, reg u256 r8, reg u256 r56
) -> reg mut ptr u256[25] {
  reg u256[5] c_571;
  reg u256 t_574;
  reg u256 t_577;
  reg u256 t_580;
  reg u256 t_583;
  reg u256 t_586;
  reg u256 t_593;
  reg u256 t_596;
  reg u256 t_599;
  reg u256 t_602;
  reg u256[5] b_606;
  reg u256 t_607;
  reg u256 t_608;
  reg u256 t_609;
  reg u256 t_610;
  reg u256 t_611;
  reg u256 t_612;
  reg u256 t_613;
  reg u256 t_614;
  reg u256 t_615;
  reg u256 t_616;
  reg u256[5] d_619;
  reg u256 t_622;
  reg u256 t_625;
  reg u256 t_628;
  reg u256 t_631;
  reg u256 t_634;
  reg u256[5] b_638;
  reg u256 t_639;
  reg u256 t_640;
  reg u256 t_641;
  reg u256 t_642;
  reg u256 t_643;
  reg u256 t_644;
  reg u256 t_645;
  reg u256 t_646;
  reg u256 t_647;
  reg u256 t_648;
  reg u256 t_655;
  reg u256 t_658;
  reg u256 t_661;
  reg u256 t_667;
  reg u256[5] b_671;
  reg u256 t_672;
  reg u256 t_673;
  reg u256 t_674;
  reg u256 t_675;
  reg u256 t_676;
  reg u256 t_677;
  reg u256 t_678;
  reg u256 t_679;
  reg u256 t_680;
  reg u256 t_681;
  reg u256 t_688;
  reg u256 t_691;
  reg u256 t_694;
  reg u256 t_697;
  reg u256[5] b_704;
  reg u256 t_705;
  reg u256 t_706;
  reg u256 t_707;
  reg u256 t_708;
  reg u256 t_709;
  reg u256 t_710;
  reg u256 t_711;
  reg u256 t_712;
  reg u256 t_713;
  reg u256 t_714;
  reg u256 t_720;
  reg u256 t_723;
  reg u256 t_726;
  reg u256 t_729;
  reg u256 t_732;
  reg u256[5] b_736;
  reg u256 t_737;
  reg u256 t_738;
  reg u256 t_739;
  reg u256 t_740;
  reg u256 t_741;
  reg u256 t_742;
  reg u256 t_743;
  reg u256 t_744;
  reg u256 t_745;
  reg u256 t_746;

  c_571[0] = a[0]; /* u256 */
  c_571[1] = a[1]; /* u256 */
  c_571[2] = a[2]; /* u256 */
  c_571[3] = a[3]; /* u256 */
  c_571[4] = a[4]; /* u256 */
  c_571[0] = (c_571[0] ^256u a[5]); /* u256 */
  c_571[1] = (c_571[1] ^256u a[6]); /* u256 */
  c_571[2] = (c_571[2] ^256u a[7]); /* u256 */
  c_571[3] = (c_571[3] ^256u a[8]); /* u256 */
  c_571[4] = (c_571[4] ^256u a[9]); /* u256 */
  c_571[0] = (c_571[0] ^256u a[10]); /* u256 */
  c_571[1] = (c_571[1] ^256u a[11]); /* u256 */
  c_571[2] = (c_571[2] ^256u a[12]); /* u256 */
  c_571[3] = (c_571[3] ^256u a[13]); /* u256 */
  c_571[4] = (c_571[4] ^256u a[14]); /* u256 */
  c_571[0] = (c_571[0] ^256u a[15]); /* u256 */
  c_571[1] = (c_571[1] ^256u a[16]); /* u256 */
  c_571[2] = (c_571[2] ^256u a[17]); /* u256 */
  c_571[3] = (c_571[3] ^256u a[18]); /* u256 */
  c_571[4] = (c_571[4] ^256u a[19]); /* u256 */
  c_571[0] = (c_571[0] ^256u a[20]); /* u256 */
  c_571[1] = (c_571[1] ^256u a[21]); /* u256 */
  c_571[2] = (c_571[2] ^256u a[22]); /* u256 */
  c_571[3] = (c_571[3] ^256u a[23]); /* u256 */
  c_571[4] = (c_571[4] ^256u a[24]); /* u256 */
  d_619[0] = c_571[1]; /* u256 */
  t_574 = #VPSLL_4u64(d_619[0], ((128u) 1)); /*  */
  d_619[0] = #VPSRL_4u64(d_619[0], ((128u) 63)); /*  */
  d_619[0] = (d_619[0] |256u t_574); /* u256 */
  d_619[0] = (d_619[0] ^256u c_571[4]); /* u256 */
  d_619[1] = c_571[2]; /* u256 */
  t_577 = #VPSLL_4u64(d_619[1], ((128u) 1)); /*  */
  d_619[1] = #VPSRL_4u64(d_619[1], ((128u) 63)); /*  */
  d_619[1] = (d_619[1] |256u t_577); /* u256 */
  d_619[1] = (d_619[1] ^256u c_571[0]); /* u256 */
  d_619[2] = c_571[3]; /* u256 */
  t_580 = #VPSLL_4u64(d_619[2], ((128u) 1)); /*  */
  d_619[2] = #VPSRL_4u64(d_619[2], ((128u) 63)); /*  */
  d_619[2] = (d_619[2] |256u t_580); /* u256 */
  d_619[2] = (d_619[2] ^256u c_571[1]); /* u256 */
  d_619[3] = c_571[4]; /* u256 */
  t_583 = #VPSLL_4u64(d_619[3], ((128u) 1)); /*  */
  d_619[3] = #VPSRL_4u64(d_619[3], ((128u) 63)); /*  */
  d_619[3] = (d_619[3] |256u t_583); /* u256 */
  d_619[3] = (d_619[3] ^256u c_571[2]); /* u256 */
  d_619[4] = c_571[0]; /* u256 */
  t_586 = #VPSLL_4u64(d_619[4], ((128u) 1)); /*  */
  d_619[4] = #VPSRL_4u64(d_619[4], ((128u) 63)); /*  */
  d_619[4] = (d_619[4] |256u t_586); /* u256 */
  d_619[4] = (d_619[4] ^256u c_571[3]); /* u256 */
  b_606[0] = a[0]; /* u256 */
  b_606[0] = (b_606[0] ^256u d_619[0]); /* u256 */
  b_606[1] = a[6]; /* u256 */
  b_606[1] = (b_606[1] ^256u d_619[1]); /* u256 */
  t_593 = #VPSLL_4u64(b_606[1], ((128u) 44)); /*  */
  b_606[1] = #VPSRL_4u64(b_606[1], ((128u) 20)); /*  */
  b_606[1] = (b_606[1] |256u t_593); /* u256 */
  b_606[2] = a[12]; /* u256 */
  b_606[2] = (b_606[2] ^256u d_619[2]); /* u256 */
  t_596 = #VPSLL_4u64(b_606[2], ((128u) 43)); /*  */
  b_606[2] = #VPSRL_4u64(b_606[2], ((128u) 21)); /*  */
  b_606[2] = (b_606[2] |256u t_596); /* u256 */
  b_606[3] = a[18]; /* u256 */
  b_606[3] = (b_606[3] ^256u d_619[3]); /* u256 */
  t_599 = #VPSLL_4u64(b_606[3], ((128u) 21)); /*  */
  b_606[3] = #VPSRL_4u64(b_606[3], ((128u) 43)); /*  */
  b_606[3] = (b_606[3] |256u t_599); /* u256 */
  b_606[4] = a[24]; /* u256 */
  b_606[4] = (b_606[4] ^256u d_619[4]); /* u256 */
  t_602 = #VPSLL_4u64(b_606[4], ((128u) 14)); /*  */
  b_606[4] = #VPSRL_4u64(b_606[4], ((128u) 50)); /*  */
  b_606[4] = (b_606[4] |256u t_602); /* u256 */
  t_607 = #VPANDN_256(b_606[1], b_606[2]); /*  */
  t_608 = (t_607 ^256u b_606[0]); /* u256 */
  e[0] = t_608; /* u256 */
  t_609 = #VPANDN_256(b_606[2], b_606[3]); /*  */
  t_610 = (t_609 ^256u b_606[1]); /* u256 */
  e[1] = t_610; /* u256 */
  t_611 = #VPANDN_256(b_606[3], b_606[4]); /*  */
  t_612 = (t_611 ^256u b_606[2]); /* u256 */
  e[2] = t_612; /* u256 */
  t_613 = #VPANDN_256(b_606[4], b_606[0]); /*  */
  t_614 = (t_613 ^256u b_606[3]); /* u256 */
  e[3] = t_614; /* u256 */
  t_615 = #VPANDN_256(b_606[0], b_606[1]); /*  */
  t_616 = (t_615 ^256u b_606[4]); /* u256 */
  e[4] = t_616; /* u256 */
  b_638[0] = a[3]; /* u256 */
  b_638[0] = (b_638[0] ^256u d_619[3]); /* u256 */
  t_622 = #VPSLL_4u64(b_638[0], ((128u) 28)); /*  */
  b_638[0] = #VPSRL_4u64(b_638[0], ((128u) 36)); /*  */
  b_638[0] = (b_638[0] |256u t_622); /* u256 */
  b_638[1] = a[9]; /* u256 */
  b_638[1] = (b_638[1] ^256u d_619[4]); /* u256 */
  t_625 = #VPSLL_4u64(b_638[1], ((128u) 20)); /*  */
  b_638[1] = #VPSRL_4u64(b_638[1], ((128u) 44)); /*  */
  b_638[1] = (b_638[1] |256u t_625); /* u256 */
  b_638[2] = a[10]; /* u256 */
  b_638[2] = (b_638[2] ^256u d_619[0]); /* u256 */
  t_628 = #VPSLL_4u64(b_638[2], ((128u) 3)); /*  */
  b_638[2] = #VPSRL_4u64(b_638[2], ((128u) 61)); /*  */
  b_638[2] = (b_638[2] |256u t_628); /* u256 */
  b_638[3] = a[16]; /* u256 */
  b_638[3] = (b_638[3] ^256u d_619[1]); /* u256 */
  t_631 = #VPSLL_4u64(b_638[3], ((128u) 45)); /*  */
  b_638[3] = #VPSRL_4u64(b_638[3], ((128u) 19)); /*  */
  b_638[3] = (b_638[3] |256u t_631); /* u256 */
  b_638[4] = a[22]; /* u256 */
  b_638[4] = (b_638[4] ^256u d_619[2]); /* u256 */
  t_634 = #VPSLL_4u64(b_638[4], ((128u) 61)); /*  */
  b_638[4] = #VPSRL_4u64(b_638[4], ((128u) 3)); /*  */
  b_638[4] = (b_638[4] |256u t_634); /* u256 */
  t_639 = #VPANDN_256(b_638[1], b_638[2]); /*  */
  t_640 = (t_639 ^256u b_638[0]); /* u256 */
  e[5] = t_640; /* u256 */
  t_641 = #VPANDN_256(b_638[2], b_638[3]); /*  */
  t_642 = (t_641 ^256u b_638[1]); /* u256 */
  e[6] = t_642; /* u256 */
  t_643 = #VPANDN_256(b_638[3], b_638[4]); /*  */
  t_644 = (t_643 ^256u b_638[2]); /* u256 */
  e[7] = t_644; /* u256 */
  t_645 = #VPANDN_256(b_638[4], b_638[0]); /*  */
  t_646 = (t_645 ^256u b_638[3]); /* u256 */
  e[8] = t_646; /* u256 */
  t_647 = #VPANDN_256(b_638[0], b_638[1]); /*  */
  t_648 = (t_647 ^256u b_638[4]); /* u256 */
  e[9] = t_648; /* u256 */
  b_671[0] = a[1]; /* u256 */
  b_671[0] = (b_671[0] ^256u d_619[1]); /* u256 */
  t_655 = #VPSLL_4u64(b_671[0], ((128u) 1)); /*  */
  b_671[0] = #VPSRL_4u64(b_671[0], ((128u) 63)); /*  */
  b_671[0] = (b_671[0] |256u t_655); /* u256 */
  b_671[1] = a[7]; /* u256 */
  b_671[1] = (b_671[1] ^256u d_619[2]); /* u256 */
  t_658 = #VPSLL_4u64(b_671[1], ((128u) 6)); /*  */
  b_671[1] = #VPSRL_4u64(b_671[1], ((128u) 58)); /*  */
  b_671[1] = (b_671[1] |256u t_658); /* u256 */
  b_671[2] = a[13]; /* u256 */
  b_671[2] = (b_671[2] ^256u d_619[3]); /* u256 */
  t_661 = #VPSLL_4u64(b_671[2], ((128u) 25)); /*  */
  b_671[2] = #VPSRL_4u64(b_671[2], ((128u) 39)); /*  */
  b_671[2] = (b_671[2] |256u t_661); /* u256 */
  b_671[3] = a[19]; /* u256 */
  b_671[3] = (b_671[3] ^256u d_619[4]); /* u256 */
  b_671[3] = #VPSHUFB_256(b_671[3], r8); /*  */
  b_671[4] = a[20]; /* u256 */
  b_671[4] = (b_671[4] ^256u d_619[0]); /* u256 */
  t_667 = #VPSLL_4u64(b_671[4], ((128u) 18)); /*  */
  b_671[4] = #VPSRL_4u64(b_671[4], ((128u) 46)); /*  */
  b_671[4] = (b_671[4] |256u t_667); /* u256 */
  t_672 = #VPANDN_256(b_671[1], b_671[2]); /*  */
  t_673 = (t_672 ^256u b_671[0]); /* u256 */
  e[10] = t_673; /* u256 */
  t_674 = #VPANDN_256(b_671[2], b_671[3]); /*  */
  t_675 = (t_674 ^256u b_671[1]); /* u256 */
  e[11] = t_675; /* u256 */
  t_676 = #VPANDN_256(b_671[3], b_671[4]); /*  */
  t_677 = (t_676 ^256u b_671[2]); /* u256 */
  e[12] = t_677; /* u256 */
  t_678 = #VPANDN_256(b_671[4], b_671[0]); /*  */
  t_679 = (t_678 ^256u b_671[3]); /* u256 */
  e[13] = t_679; /* u256 */
  t_680 = #VPANDN_256(b_671[0], b_671[1]); /*  */
  t_681 = (t_680 ^256u b_671[4]); /* u256 */
  e[14] = t_681; /* u256 */
  b_704[0] = a[4]; /* u256 */
  b_704[0] = (b_704[0] ^256u d_619[4]); /* u256 */
  t_688 = #VPSLL_4u64(b_704[0], ((128u) 27)); /*  */
  b_704[0] = #VPSRL_4u64(b_704[0], ((128u) 37)); /*  */
  b_704[0] = (b_704[0] |256u t_688); /* u256 */
  b_704[1] = a[5]; /* u256 */
  b_704[1] = (b_704[1] ^256u d_619[0]); /* u256 */
  t_691 = #VPSLL_4u64(b_704[1], ((128u) 36)); /*  */
  b_704[1] = #VPSRL_4u64(b_704[1], ((128u) 28)); /*  */
  b_704[1] = (b_704[1] |256u t_691); /* u256 */
  b_704[2] = a[11]; /* u256 */
  b_704[2] = (b_704[2] ^256u d_619[1]); /* u256 */
  t_694 = #VPSLL_4u64(b_704[2], ((128u) 10)); /*  */
  b_704[2] = #VPSRL_4u64(b_704[2], ((128u) 54)); /*  */
  b_704[2] = (b_704[2] |256u t_694); /* u256 */
  b_704[3] = a[17]; /* u256 */
  b_704[3] = (b_704[3] ^256u d_619[2]); /* u256 */
  t_697 = #VPSLL_4u64(b_704[3], ((128u) 15)); /*  */
  b_704[3] = #VPSRL_4u64(b_704[3], ((128u) 49)); /*  */
  b_704[3] = (b_704[3] |256u t_697); /* u256 */
  b_704[4] = a[23]; /* u256 */
  b_704[4] = (b_704[4] ^256u d_619[3]); /* u256 */
  b_704[4] = #VPSHUFB_256(b_704[4], r56); /*  */
  t_705 = #VPANDN_256(b_704[1], b_704[2]); /*  */
  t_706 = (t_705 ^256u b_704[0]); /* u256 */
  e[15] = t_706; /* u256 */
  t_707 = #VPANDN_256(b_704[2], b_704[3]); /*  */
  t_708 = (t_707 ^256u b_704[1]); /* u256 */
  e[16] = t_708; /* u256 */
  t_709 = #VPANDN_256(b_704[3], b_704[4]); /*  */
  t_710 = (t_709 ^256u b_704[2]); /* u256 */
  e[17] = t_710; /* u256 */
  t_711 = #VPANDN_256(b_704[4], b_704[0]); /*  */
  t_712 = (t_711 ^256u b_704[3]); /* u256 */
  e[18] = t_712; /* u256 */
  t_713 = #VPANDN_256(b_704[0], b_704[1]); /*  */
  t_714 = (t_713 ^256u b_704[4]); /* u256 */
  e[19] = t_714; /* u256 */
  b_736[0] = a[2]; /* u256 */
  b_736[0] = (b_736[0] ^256u d_619[2]); /* u256 */
  t_720 = #VPSLL_4u64(b_736[0], ((128u) 62)); /*  */
  b_736[0] = #VPSRL_4u64(b_736[0], ((128u) 2)); /*  */
  b_736[0] = (b_736[0] |256u t_720); /* u256 */
  b_736[1] = a[8]; /* u256 */
  b_736[1] = (b_736[1] ^256u d_619[3]); /* u256 */
  t_723 = #VPSLL_4u64(b_736[1], ((128u) 55)); /*  */
  b_736[1] = #VPSRL_4u64(b_736[1], ((128u) 9)); /*  */
  b_736[1] = (b_736[1] |256u t_723); /* u256 */
  b_736[2] = a[14]; /* u256 */
  b_736[2] = (b_736[2] ^256u d_619[4]); /* u256 */
  t_726 = #VPSLL_4u64(b_736[2], ((128u) 39)); /*  */
  b_736[2] = #VPSRL_4u64(b_736[2], ((128u) 25)); /*  */
  b_736[2] = (b_736[2] |256u t_726); /* u256 */
  b_736[3] = a[15]; /* u256 */
  b_736[3] = (b_736[3] ^256u d_619[0]); /* u256 */
  t_729 = #VPSLL_4u64(b_736[3], ((128u) 41)); /*  */
  b_736[3] = #VPSRL_4u64(b_736[3], ((128u) 23)); /*  */
  b_736[3] = (b_736[3] |256u t_729); /* u256 */
  b_736[4] = a[21]; /* u256 */
  b_736[4] = (b_736[4] ^256u d_619[1]); /* u256 */
  t_732 = #VPSLL_4u64(b_736[4], ((128u) 2)); /*  */
  b_736[4] = #VPSRL_4u64(b_736[4], ((128u) 62)); /*  */
  b_736[4] = (b_736[4] |256u t_732); /* u256 */
  t_737 = #VPANDN_256(b_736[1], b_736[2]); /*  */
  t_738 = (t_737 ^256u b_736[0]); /* u256 */
  e[20] = t_738; /* u256 */
  t_739 = #VPANDN_256(b_736[2], b_736[3]); /*  */
  t_740 = (t_739 ^256u b_736[1]); /* u256 */
  e[21] = t_740; /* u256 */
  t_741 = #VPANDN_256(b_736[3], b_736[4]); /*  */
  t_742 = (t_741 ^256u b_736[2]); /* u256 */
  e[22] = t_742; /* u256 */
  t_743 = #VPANDN_256(b_736[4], b_736[0]); /*  */
  t_744 = (t_743 ^256u b_736[3]); /* u256 */
  e[23] = t_744; /* u256 */
  t_745 = #VPANDN_256(b_736[0], b_736[1]); /*  */
  t_746 = (t_745 ^256u b_736[4]); /* u256 */
  e[24] = t_746; /* u256 */
  return (e);
}


"#

/-- `src/amd64/avx2/keccakf1600x4.jinc`: the four-way permutation
    `_keccakf1600_avx2x4` with its round loop, the byte-shuffle masks `ROL8` and
    `ROL56`, and the packing between four scalar states and the four-way state. -/
def keccakX4Src : String := r#"from Keccak require "common/keccakf1600_generic.jinc"

type keccakx4_state = u256[25];

require "keccakf1600x4_pround_inlined.jinc"

u256 ROL56 = 0x181F1E1D1C1B1A191017161514131211080F0E0D0C0B0A090007060504030201;
u256 ROL8  = 0x1E1D1C1B1A19181F16151413121110170E0D0C0B0A09080F0605040302010007;


inline fn __keccakf1600_avx2x4
( reg ptr u256[25] a
) -> reg ptr u256[25]
{
  reg ptr u64[24] RC;

  stack u256[25] s_e;
  reg ptr u256[25] e;

  reg u256 rc r8 r56 t;
  reg ui64 c;

  RC = KECCAK1600_RC;
  e = s_e;
  r8 = ROL8;
  r56 = ROL56;

  c = 0;
  while(c < KECCAK_ROUNDS)
  {
    rc = #VPBROADCAST_4u64(RC[c]);

    e = _keccakf1600_4x_pround(e, a, r8, r56);
    t = rc ^ e[0];
    e[0] = t;

    a, e = #swap(e, a);

    rc = #VPBROADCAST_4u64(RC[c+1]);
    a = _keccakf1600_4x_pround(a, e, r8, r56);
    t = rc ^ a[0];
    a[0] = t;

    a, e = #swap(e, a);

    c += 2;
  }

  return a;
}

fn _keccakf1600_avx2x4
( reg ptr u256[25] a
) -> reg ptr u256[25]
{
  a = __keccakf1600_avx2x4(a);
  return a;
}

inline fn _keccakf1600_avx2x4_
( reg ptr u256[25] a
) -> reg ptr u256[25]
{
  a = a;
  a = _keccakf1600_avx2x4(a);
  a = a;
  return a;
}

// pack 4 keccak states (st25) into a 4-way state (st4x)
inline fn __u256x4_4u64x4
( reg u256 x0 x1 x2 x3
) -> reg u256, reg u256, reg u256, reg u256 {
  // x0 = l00 l01  l02 l03
  // x1 = l10 l11  l12 l13
  // x2 = l20 l21  l22 l23
  // x3 = l30 l31  l32 l33
  reg u256 y0, y1, y2, y3;
  y0 = #VPUNPCKL_4u64(x0, x1);	// y0 = l00 l10  l02 l12
  y1 = #VPUNPCKH_4u64(x0, x1);	// y1 = l01 l11  l03 l13
  y2 = #VPUNPCKL_4u64(x2, x3);	// y2 = l20 l30  l22 l32
  y3 = #VPUNPCKH_4u64(x2, x3);	// y3 = l21 l31  l23 l33

  x0 = #VPERM2I128(y0, y2, 0x20);	// x0 = l00 l10  l20 l30
  x1 = #VPERM2I128(y1, y3, 0x20);	// x1 = l01 l11  l21 l31
  x2 = #VPERM2I128(y0, y2, 0x31);	// x2 = l02 l12  l22 l32
  x3 = #VPERM2I128(y1, y3, 0x31);	// x3 = l03 l13  l23 l33

  return x0, x1, x2, x3;
}

#[safety =
   { requires = is_arr_init(st0,0,25*8) && is_arr_init(st1,0,25*8)
             && is_arr_init(st2,0,25*8) && is_arr_init(st3,0,25*8)
   , ensures = is_arr_init(st4x,0,25*32)
   }
 ]
inline fn __st4x_pack
( reg mut ptr u256[25] st4x
, reg const ptr u64[25] st0 st1 st2 st3
) -> reg ptr u256[25]
{
  inline int i;
  reg u256 x0, x1, x2, x3;
  reg u64 t0, t1, t2, t3;
  for i = 0 to 6 {
    x0 = st0[:u256 i];
    x1 = st1[:u256 i];
    x2 = st2[:u256 i];
    x3 = st3[:u256 i];
    x0, x1, x2, x3 = __u256x4_4u64x4(x0, x1, x2, x3);
    st4x[4*i+0] = x0;
    st4x[4*i+1] = x1;
    st4x[4*i+2] = x2;
    st4x[4*i+3] = x3;
  }
  t0 = st0[24];
  t1 = st1[24];
  t2 = st2[24];
  t3 = st3[24];
  st4x[:u64 4*24+0] = t0;
  st4x[:u64 4*24+1] = t1;
  st4x[:u64 4*24+2] = t2;
  st4x[:u64 4*24+3] = t3;

  return st4x;
}



// extracts 4 keccak states (st25) from a 4-way state (st4x)
inline fn __4u64x4_u256x4
( reg u256 y0 y1 y2 y3
) -> reg u256, reg u256, reg u256, reg u256 {
  // y0 = l00 l10  l20 l30
  // y1 = l01 l11  l21 l31
  // y2 = l02 l12  l22 l32
  // y3 = l03 l13  l23 l33
  reg u256 x0, x1, x2, x3;
  x0 = #VPERM2I128(y0, y2, 0x20);	// x0 = l00 l10  l02 l12
  x1 = #VPERM2I128(y1, y3, 0x20);	// x1 = l01 l11  l03 l13
  x2 = #VPERM2I128(y0, y2, 0x31);	// x2 = l20 l30  l22 l32
  x3 = #VPERM2I128(y1, y3, 0x31);	// x3 = l21 l31  l23 l33

  y0 = #VPUNPCKL_4u64(x0, x1);	// y0 = l00 l01  l02 l03
  y1 = #VPUNPCKH_4u64(x0, x1);	// y1 = l10 l11  l12 l13
  y2 = #VPUNPCKL_4u64(x2, x3);	// y2 = l20 l21  l22 l23
  y3 = #VPUNPCKH_4u64(x2, x3);	// y3 = l30 l31  l32 l33

  return y0, y1, y2, y3;
}

#[safety =
   { requires = is_arr_init(st4x,0,25*32)
   , ensures = is_arr_init(st0,0,25*8) && is_arr_init(st1,0,25*8)
            && is_arr_init(st2,0,25*8) && is_arr_init(st3,0,25*8)
   }
 ]
inline fn __st4x_unpack
( reg mut ptr u64[25] st0 st1 st2 st3
, reg const ptr u256[25] st4x
) -> reg ptr u64[25], reg ptr u64[25], reg ptr u64[25], reg ptr u64[25]
{
  inline int i;
  reg u256 x0, x1, x2, x3;
  reg u64 t0, t1, t2, t3;
  for i = 0 to 6 {
    x0 = st4x[:u256 4*i+0];
    x1 = st4x[:u256 4*i+1];
    x2 = st4x[:u256 4*i+2];
    x3 = st4x[:u256 4*i+3];
    x0, x1, x2, x3 = __4u64x4_u256x4(x0, x1, x2, x3);
    st0.[:u256 4*8*i] = x0;
    st1.[:u256 4*8*i] = x1;
    st2.[:u256 4*8*i] = x2;
    st3.[:u256 4*8*i] = x3;
  }
  t0 = st4x[:u64 4*24+0];
  t1 = st4x[:u64 4*24+1];
  t2 = st4x[:u64 4*24+2];
  t3 = st4x[:u64 4*24+3];
  st0[24] = t0;
  st1[24] = t1;
  st2[24] = t2;
  st3[24] = t3;

  return st0, st1, st2, st3;
}


/* For testing:
export fn testF_avx2x4(reg mut ptr u256[25] st) -> reg ptr u256[25] {
 st = _keccakf1600_avx2x4(st);
 return st;
}
*/

/* For the BDEP proof... */
inline fn __keccakf1600_pround_unpacked
( reg mut ptr u64[25] st0 st1 st2 st3
) -> reg ptr u64[25], reg ptr u64[25], reg ptr u64[25], reg ptr u64[25] {
  stack u256[25] st4x1, st4x2;
  reg u256 r8 r56;

  r8 = ROL8;
  r56 = ROL56;
  st4x1 = __st4x_pack( st4x1, st0, st1, st2, st3);
  st4x2 = _keccakf1600_4x_pround(st4x2, st4x1, r8, r56);
  st0, st1, st2, st3 = __st4x_unpack(st0, st1, st2, st3, st4x2);

  return st0, st1, st2, st3;
}

#[safety =
   { requires = is_arr_init(a,0,32*25)
   , ensures = is_arr_init(e,0,32*25)
   }
 ]
inline fn __keccakf1600_pround_equiv
( reg mut ptr u256[25] e
, reg const ptr u256[25] a
) -> reg ptr u256[25] {
  stack u64[25] st0, st1, st2, st3;

  st0, st1, st2, st3 = __st4x_unpack(st0, st1, st2, st3, a);
  st0, st1, st2, st3 = __keccakf1600_pround_unpacked(st0, st1, st2, st3);
  e = __st4x_pack( e, st0, st1, st2, st3);

  return e;
}
"#

/-- The entry point of the four-way import: `out` receives the 25 lanes of `inp`,
    each the 256-bit cell holding lane `i` of the four states, then the four-way
    permutation in place. -/
def keccakX4WrapperSrc : String := r#"export fn keccak_f1600_x4(reg ptr u256[25] out inp) -> reg ptr u256[25]
{
  inline int i;
  reg u256 t;
  for i = 0 to 25 { t = inp[i]; out[i] = t; }
  out = _keccakf1600_avx2x4(out);
  return out;
}
"#

/-- The four-way source unit: the generic constants, the round, the permutation
    and the entry point, in dependency order. -/
def keccakX4Unit : String :=
  keccakGenericSrc ++ keccakX4PRoundSrc ++ keccakX4Src ++ keccakX4WrapperSrc

/-- The exported four-way symbol, the name of the owned four-way kernel. -/
def keccakF1600X4Sym : String := "keccak_f1600_x4"

/-- `keccak_f1600_x4` imported with its round loop kept rolled: the twelve trips
    of the `while`, two rounds each, are one `for` over the trip index, and the
    broadcast round constants are 256-bit loads from `KECCAK1600_RC_bcast4u64` at
    the indices `2·idx` and `2·idx + 1`. -/
def keccakF1600X4Rolled : Except String JincInline.RolledImport :=
  JincInline.importFunRolled keccakX4Unit keccakF1600X4Sym

/-- The owned AT&T rendering of `keccakF1600X4Rolled`
    (`JincElab.emitJFunRolledAsm`), or the import error as an assembler
    comment. -/
def keccakF1600X4RolledAsm : String :=
  match keccakF1600X4Rolled with
  | .ok r => JincElab.emitJFunRolledAsm r.fn r.tables keccakF1600X4Sym
  | .error e => s!"; import error: {e}"

end CatCrypt.Crypto.Jasmin.KeccakJincImport
