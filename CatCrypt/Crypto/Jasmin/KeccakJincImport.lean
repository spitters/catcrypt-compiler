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
def keccakSpongeSyms : List String := ["sha3_256_jinc", "shake128_jinc", "shake256_jinc"]

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

end CatCrypt.Crypto.Jasmin.KeccakJincImport
