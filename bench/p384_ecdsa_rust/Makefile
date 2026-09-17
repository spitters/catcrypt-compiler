# Leaf shims, KATs and a benchmark for the CatCrypt-emitted P-384 ECDSA
# source.
#
# Our side is the emitted orchestration in gen/ over a leaf backend; the
# field and the group law under those leaves are adopted verified leaves
# (fiat-crypto, AUCurves p384-safe-rust, AWS s2n-bignum), and the reference
# side is RustCrypto p384 and Graviola, external unverified implementations.
# See the README for which side is which, PERF.md for recorded results.
# No target here runs Lean; `field` reads two emitted `.s` files that lake
# writes (README, § Paths).
#
#   make test        # every test, every backend, pure-Rust AUCurves field
#   make kat         # the FIPS 186-4 CAVP vectors only
#   make wycheproof  # the Wycheproof adversarial verify corpus only
#   make graviola    # the Graviola cross-implementation interop suite only
#   make bench       # both AUCurves configurations, pinned, round-robin
#   make field       # the P-384 field multiply: our emitted kernels vs s2n
#   make test-no-s2n # the two AUCurves backends alone, s2n feature off
#   make production  # OpenSSL + BoringSSL + AWS-LC interop suite, both field configs
#   make dhkem       # DHKEM(P-384) suites, with and without the C libraries
#   make bench-dhkem # DHKEM(P-384) benchmark, three AUCurves field configs
#   make bench-production  # the benchmark with OpenSSL, BoringSSL and AWS-LC columns
#   make clean

CARGO ?= cargo --offline
# The s2n-bignum checkout; build.rs links $(S2N_BIGNUM_DIR)/x86/libs2nbignum.a.
# The default is the checkout in the sibling SSProve-lean tree.
S2N_BIGNUM_DIR ?= $(abspath ../../../SSProve-lean/bench/reference_install/s2n-bignum)
export S2N_BIGNUM_DIR
# The s2n-bignum leaf backend is behind a feature so the other backends can
# be built without the archive; every target below turns it on.
FEATURES ?= --features s2n
# The production TLS-stack opponents: BoringSSL linked statically, OpenSSL's
# system libcrypto.so.3 and AWS-LC's libcrypto.so opened at run time.  See
# build.rs and src/awslc.rs.
PROD_FEATURES ?= --features s2n,production
# The CryptOpt assembly is x86-64-only and is linked by p384-safe-rust's
# build script; this forces the pure-Rust field leaves instead.
PURE  := P384_NO_CRYPTOPT=1
# Wycheproof vectors are not vendored.  The corpus test skips when absent.
WYCHEPROOF_DIR ?= $(HOME)/Claude/bench_refs/boringssl/third_party/wycheproof_testvectors
# Core to pin the benchmark to; leave empty to let the scheduler choose.
BENCH_CPU ?= 15
BENCH_REPS ?= 15
BENCH_ITERS ?= 300
# Iterations per repetition for the scalar-inverse and two-term-multiply
# micro-benchmarks, which measure much cheaper operations.
BENCH_MICRO_ITERS ?= 4000

# Known-answer gate and sample count for the field-multiply comparison.
FIELD_KAT ?= 100000
FIELD_SAMPLES ?= 301
FIELD_INNER ?= 2000

.PHONY: test test-asm test-no-s2n kat wycheproof graviola graviola-asm \
        production production-asm bench-production bench-production-pure \
        bench-production-asm bench bench-pure bench-asm field field-pure \
        field-asm clean

test:
	$(PURE) WYCHEPROOF_DIR=$(WYCHEPROOF_DIR) $(CARGO) test --release $(FEATURES) -- --nocapture

# The same tests with the CryptOpt assembly linked, which exercises a
# different pair of field leaves under the AUCurves group law.  The
# s2n-bignum backend is unaffected by that choice and is scored again here,
# which makes the two runs a check on each other.
test-asm:
	WYCHEPROOF_DIR=$(WYCHEPROOF_DIR) $(CARGO) test --release $(FEATURES) -- --nocapture

# The two AUCurves backends with the s2n feature off, which is how the crate
# builds where the archive is absent.
test-no-s2n:
	$(PURE) WYCHEPROOF_DIR=$(WYCHEPROOF_DIR) $(CARGO) test --release -- --nocapture

kat:
	$(PURE) $(CARGO) test --release $(FEATURES) --test cavp -- --nocapture

wycheproof:
	$(PURE) WYCHEPROOF_DIR=$(WYCHEPROOF_DIR) $(CARGO) test --release $(FEATURES) --test wycheproof -- --nocapture

# Cross-implementation interop against Graviola, whose P-384 arithmetic is
# the same s2n-bignum assembly the `s2n` backend runs.  Both AUCurves field
# configurations, since the marshalling is the same but the leaves under it
# are not.
graviola: graviola-asm
	$(PURE) $(CARGO) test --release $(FEATURES) --test graviola -- --nocapture

graviola-asm:
	$(CARGO) test --release $(FEATURES) --test graviola -- --nocapture

# Cross-implementation interop against OpenSSL 3.0 and BoringSSL, including
# every published field of the CAVP vectors through each library's
# nonce-supplied signing.
production: production-asm
	$(PURE) $(CARGO) test --release $(PROD_FEATURES) --test production -- --nocapture

production-asm:
	$(CARGO) test --release $(PROD_FEATURES) --test production -- --nocapture

bench-production: bench-production-asm bench-production-pure

bench-production-asm:
	$(CARGO) build --release $(PROD_FEATURES) --bin bench
	BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  BENCH_MICRO_ITERS=$(BENCH_MICRO_ITERS) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet $(PROD_FEATURES) --bin bench

bench-production-pure:
	$(PURE) $(CARGO) build --release $(PROD_FEATURES) --bin bench
	$(PURE) BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  BENCH_MICRO_ITERS=$(BENCH_MICRO_ITERS) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet $(PROD_FEATURES) --bin bench

# The two AUCurves configurations cannot be interleaved in one process:
# whether the CryptOpt assembly is linked is a compile-time cfg of
# p384-safe-rust.  Each process interleaves every backend against RustCrypto
# and Graviola round-robin.
bench: bench-asm bench-pure

bench-asm:
	$(CARGO) build --release $(FEATURES) --bin bench
	BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  BENCH_MICRO_ITERS=$(BENCH_MICRO_ITERS) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet $(FEATURES) --bin bench

bench-pure:
	$(PURE) $(CARGO) build --release $(FEATURES) --bin bench
	$(PURE) BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  BENCH_MICRO_ITERS=$(BENCH_MICRO_ITERS) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet $(FEATURES) --bin bench

# The P-384 field multiply on its own: the two CatCrypt-emitted kernels
# against s2n-bignum's, with a GMP-free known-answer gate whose oracle is
# s2n-bignum itself.  The emitted `.s` files live in sibling bench
# directories and are read, never regenerated; regenerate them with lake
# before recording a figure.
field: field-asm field-pure

field-pure:
	$(PURE) $(CARGO) build --release --features s2n,emit-field --bin fieldbench
	$(PURE) KAT_RANDOM=$(FIELD_KAT) FIELD_SAMPLES=$(FIELD_SAMPLES) FIELD_INNER=$(FIELD_INNER) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet --features s2n,emit-field --bin fieldbench

field-asm:
	$(CARGO) build --release --features s2n,emit-field --bin fieldbench
	KAT_RANDOM=$(FIELD_KAT) FIELD_SAMPLES=$(FIELD_SAMPLES) FIELD_INNER=$(FIELD_INNER) \
	  taskset -c $(BENCH_CPU) $(CARGO) run --release --quiet --features s2n,emit-field --bin fieldbench

# DHKEM(P-384, HKDF-SHA384): the kernel suite against the reference,
# hpke-rs and Graviola, then the C-library suite (BoringSSL, OpenSSL 3.0,
# and OpenSSL 3.6 where present).
dhkem:
	$(PURE) $(CARGO) test --release $(PROD_FEATURES) --test dhkem --test dhkem_production -- --nocapture

# The AUCurves field under the s2n-bignum archive, the third configuration.
S2N_FIELD ?= $(S2N_BIGNUM_DIR)/x86/libs2nbignum.a

.PHONY: dhkem bench-dhkem
bench-dhkem:
	$(PURE) $(CARGO) build --release $(PROD_FEATURES) --bin bench
	$(PURE) BENCH_SECTIONS=dhkem BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  taskset -c $(BENCH_CPU) ./target/release/bench
	$(CARGO) build --release $(PROD_FEATURES) --bin bench
	BENCH_SECTIONS=dhkem BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  taskset -c $(BENCH_CPU) ./target/release/bench
	P384_S2N_FIELD=$(S2N_FIELD) $(CARGO) build --release $(PROD_FEATURES) --bin bench
	P384_S2N_FIELD=$(S2N_FIELD) BENCH_SECTIONS=dhkem BENCH_REPS=$(BENCH_REPS) BENCH_ITERS=$(BENCH_ITERS) \
	  taskset -c $(BENCH_CPU) ./target/release/bench

clean:
	$(CARGO) clean 2>/dev/null || true
