# Mersenne-31 (M31) field kernels, emitted from CatCrypt's verified front and
# KAT'd byte-exact vs a direct `__int128 % p` C reference.
#
# Field:  GF(p), p = 2^31 - 1 = 2147483647 (Mersenne-31) — the CircleSTARK /
#         Plonky3-M31 / Stwo base field. 2^31 == 1 (mod p), so reduce is the
#         Mersenne double fold (v & p) + (v >> 31) plus one branch-free
#         conditional subtract; add is sum + one conditional subtract.
#
# Kernels (SysV pointer ABI, one u64 cell per pointer; all constant-time):
#   m31_mul_owned(out, a, b)     out[0] = a[0]*b[0] mod p     (a, b in [0,p))
#   m31_add_owned(out, a, b)     out[0] = a[0]+b[0] mod p     (a, b in [0,p))
#   m31_reduce_owned(out, x)     out[0] = x[0] mod p          (x < 2^62)
#
# Pipeline (owned, no jasminc, no hand Com/Lcmd):
#   CatCrypt.Crypto.SecureCompilation.Mersenne31FrontEmit
#     (LowCT body -> translateDialectControl -> cryptoDialectToJasminCom
#      -> Com.toLprogPhysAbi -> renderLprogAtt)
#     --(m31_field_from_front_emit.lean)-->  gen_com/m31_field_owned.s
#     --(cc + m31_field_kat.c)------------->  ./m31_field_kat
#
# Proof coverage: the same closed Mersenne folds carry forall-quantified
# denote=spec + `% p` + ZMod (2^31-1) field ties through the compile-from-hax
# leaves (CompileFromHaxMersenne31 mul, CompileFromHaxMersenne31Add add/reduce);
# the front-emit module gates denote=spec vs the independent Nat `% p` spec
# in-model (native_decide) and this KAT gates the deployed bytes.
#
# Targets:
#   make emit-m31-owned   # (re)emit gen_com/m31_field_owned.s from Lean
#   make m31-kat          # KAT + light cyc/op bench vs the C reference
#   make clean
#
# Vars:  CC=cc, PIN='taskset -c 0'

CC  ?= cc
PIN ?= taskset -c 0
COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: emit-m31-owned m31-kat clean

emit-m31-owned:
	$(LEAN_IN_COMPILER) lean --run bench/m31_compare/m31_field_from_front_emit.lean

gen_com/m31_field_owned.s: m31_field_from_front_emit.lean
	$(LEAN_IN_COMPILER) lean --run bench/m31_compare/m31_field_from_front_emit.lean

# KAT: edge vectors + small exhaustive (256^2) + boundary band ([p-256,p)^2) +
# 1M random vectors, byte-exact vs the direct `__int128 % p` reference
# (canonical-residue semantics of plonky3 Mersenne31 / Stwo M31).
m31-kat: gen_com/m31_field_owned.s m31_field_kat.c
	$(CC) -O2 -o m31_field_kat m31_field_kat.c gen_com/m31_field_owned.s
	$(PIN) ./m31_field_kat

clean:
	rm -f gen_com/m31_field_owned.s m31_field_kat
