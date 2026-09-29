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

The executable `keccak-jinc-emit` (`KeccakJincEmit.lean`) writes the rendering;
the bench harness `bench/keccak_compare` checks it against FIPS 202.

## Main definitions

* `keccakUnit`: the concatenated source unit.
* `keccakF1600JFun`: the imported straight-line `JFun` of `keccak_f1600`.
* `keccakF1600Asm`: its owned AT&T rendering.
* `keccakF1600Rolled`, `keccakF1600RolledAsm`: the import with the round loop
  kept rolled, and its owned AT&T rendering.
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

end CatCrypt.Crypto.Jasmin.KeccakJincImport
