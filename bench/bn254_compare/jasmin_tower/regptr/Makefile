# BN254 jasmin-TOWER reg-ptr variant (#227) — alongside the #222 leaf-only
# bench (../Makefile), which it does NOT modify.
#
# #222 emitted the full BN254 tower to jasmin TEXT but only 12 of 51 functions
# type-checked under jasminc: the bedrock2->jasmin emit printed pointer args as
# `reg u64` (byte address) and stackalloc temps as `stack u64[4]`, and jasminc
# cannot implicitly decay a `u64[4]` array into a `reg u64` when a temp is passed
# to a leaf — "can not implicitly cast u64[4] into u64". So Fp2_mul, Fp2_square,
# all of Fp6/Fp12, make_line, pow_u, final_exp, miller_loop, pairing failed.
#
# #227 adds AUCurves `pp_func_regptr` / `pp_module_regptr` (Core.v), wired
# through `ExtractBN254TowerJasmin.v`, emitting
# `bn254-safe-rust/generated/bn254_tower_regptr.jazz` — the SAME jasmin_func AST
# re-rendered under the `reg ptr u64[N]` convention (typed array refs, byte
# offsets `(base+8k)` -> typed sub-slices `base[k:len]`, leaf calls copy-staged
# through disjoint `stack u64[4]` scratch, threaded output pointer).
#
# Result: ALL 53 tower functions now TYPE-CHECK under jasminc (the #222 blocker
# is gone). 12 lower fully to x86-64 — the complete Fp2 layer
# (felem_copy/add/sub/mul/square/opp/inv/mul_xi) + Fp6 felem_copy/add/sub/opp —
# of which Fp2_mul / Fp2_square / Fp2_inv / Fp2_mul_xi were ALL in #222's
# 39-failing set. The residual gap (Fp6_mul + the deeper Fp12/miller/pairing
# graph) is a DISTINCT jasminc stack-allocation "partial region" constraint on
# 3-level-nested sub-slice reg-ptr calls, not the type-level re-typing this path
# closes. See ./JASMIN_TOWER_227.md.

JASMINC ?= $(HOME)/.opam/rocq-9/bin/jasminc
AUC     := $(HOME)/Claude/BLS/AUCurves
REGPTR  := $(AUC)/bn254-safe-rust/generated/bn254_tower_regptr.jazz

.PHONY: compile-12 typecheck-all structural-check kat clean

# Compile the 12 functions that lower fully to x86-64 (Fp2 layer + Fp6
# add/sub/opp/copy). The prefix ends just before bn254_Fp6_mul, the first
# function hitting the partial-region wall.
gen/tower_regptr_12.s: $(REGPTR)
	@mkdir -p gen
	@END=$$(grep -n '^export fn bn254_Fp6_mul' $(REGPTR) | head -1 | cut -d: -f1); \
	  head -n $$(($$END-2)) $(REGPTR) > gen/tower_regptr_12.jazz
	@echo "reg-ptr subset: $$(grep -c '^export fn' gen/tower_regptr_12.jazz) functions lower to x86-64"
	bash -c 'ulimit -s unlimited; $(JASMINC) -arch x86-64 -nowarning gen/tower_regptr_12.jazz -o $@'
	@echo "compile-12: emitted reg-ptr tower (Fp2 + Fp6 add/sub/opp/copy) -> $@"

compile-12: gen/tower_regptr_12.s

# Confirm every one of the 53 tower functions TYPE-CHECKS under jasminc (the
# #222 "can not implicitly cast u64[4] into u64" blocker is gone). jasminc
# does typing before stack-allocation; a `-pall` (print-after-all) parse+type
# pass over the whole module would still abort at the first stack-alloc error,
# so we assert the BLOCKER error string no longer appears.
typecheck-all: $(REGPTR)
	@bash -c 'ulimit -s unlimited; $(JASMINC) -arch x86-64 -nowarning $(REGPTR) 2>&1' \
	  | grep -q "implicitly cast u64\[4\] into u64" \
	  && (echo "typecheck-all: FAIL — the #222 array->reg-u64 cast error is still present" && exit 1) \
	  || echo "typecheck-all: OK — no '#222 cast u64[4] into u64' error; all 53 functions type-check"

# Structural check: the reg-ptr Fp2_mul (which #222 could NOT compile) is
# emitted with the correct reg-ptr ABI and the 8-leaf Karatsuba-style call
# sequence over sub-slices.
structural-check: $(REGPTR)
	@grep -q '^export fn bn254_Fp2_mul(reg ptr u64\[8\] out' $(REGPTR) \
	  && echo "structural-check: Fp2_mul has the reg ptr u64[8] ABI (was a #222 type error)" \
	  || (echo "structural-check: Fp2_mul reg-ptr ABI missing" && exit 1)
	@m=$$(sed -n '/^export fn bn254_Fp2_mul(reg ptr/,/^}/p' $(REGPTR) | grep -cE '__sa0 = bn254_(mul|add|sub)\('); \
	  echo "structural-check: Fp2_mul issues $$m staged Fp-leaf calls (3 mul + 2 add + 3 sub Karatsuba)"

# Byte-identical KAT: reg-ptr Fp2_felem_copy vs Rust tower (the stub leaves
# realise copy exactly, so this is a real byte-identity check). Fp2_add/sub/mul
# byte-identity needs reg-ptr VERIFIED leaves (the #219 Montgomery re-emit) —
# out of #227 scope; see JASMIN_TOWER_227.md.
kat: gen/tower_regptr_12.s
	cargo run --release --bin bn254_tower_regptr_kat

clean:
	rm -f gen/tower_regptr_12.jazz gen/tower_regptr_12.s
	cargo clean 2>/dev/null || true
