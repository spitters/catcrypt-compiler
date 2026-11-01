# bytes_direct_pallas_fesub: verified-bytes-direct + text-path differential
# KAT for the Pasta Pallas base-field subtract (completed masked add-back).
#
# Concrete instantiation of the prime-parametrized completed subtract
# (EcFeSubComplete.feSubFrameComplete / EcFeSubPastaComplete.feSubFrameAtPallas_value).
#
#   make emit             -- regenerate gen/pallas_fe_sub_bytes.o (ELF .o BYTES
#                            from the verified encoder, NO assembler) and the .s
#   make fesub-bytes-kat  -- build + run the KAT (links the bytes-direct .o
#                            directly; assembles the text .s with `as`; both vs GMP)

GEN  := gen
CC   := cc
AS   := as
CFLAGS := -O2

COMPILER := $(abspath $(CURDIR)/../..)
# Lake root: a sibling development checkout when present, this repository otherwise.
DEV      := $(or $(wildcard $(abspath $(COMPILER)/../SSProve-lean)),$(COMPILER))
# lake env/build from the dev root (one-root rule); the command runs in the compiler tree
LEAN_IN_COMPILER := cd $(DEV) && lake env sh -c 'cd $(COMPILER) && exec "$$@"' sh

.PHONY: emit fesub-bytes-kat clean

emit:
	$(LEAN_IN_COMPILER) lean bench/bytes_direct_pallas_fesub/fesub_bytes_emit.lean

$(GEN)/pallas_fe_sub_text.o: $(GEN)/pallas_fe_sub_text.s
	$(AS) --64 $< -o $(GEN)/pallas_fe_sub_text_raw.o
	objcopy --redefine-sym pallas_fe_sub=pallas_fe_subt $(GEN)/pallas_fe_sub_text_raw.o $(GEN)/pallas_fe_sub_text.o

$(GEN)/pallas_fe_sub_bytes.o: emit

fesub-bytes-kat: fesub_kat.c $(GEN)/pallas_fe_sub_bytes.o $(GEN)/pallas_fe_sub_text.o
	$(CC) $(CFLAGS) fesub_kat.c $(GEN)/pallas_fe_sub_bytes.o $(GEN)/pallas_fe_sub_text.o -lgmp -o fesub-bytes-kat
	./fesub-bytes-kat

clean:
	rm -f $(GEN)/*.o fesub-bytes-kat
