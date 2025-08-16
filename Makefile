SHELL := /bin/bash

# Host compiler for the emulator
CC      ?= cc
CFLAGS  ?= -std=c11 -O2

# RISC-V cross toolchain for building the sample ELF
# Override as needed, e.g. `make RV_CC=clang run`
RV_CC   ?= riscv64-unknown-elf-gcc

# Detect clang usage to adjust flags
RV_CC_BASENAME := $(notdir $(RV_CC))
ifeq ($(findstring clang,$(RV_CC_BASENAME)),clang)
  RV_TARGET_FLAGS := --target=riscv64
  # Ensure the first PT_LOAD segment starts at 0x80000000
  RV_LDFLAGS      := -nostartfiles -nostdlib -static -Wl,-Ttext-segment=0x80000000
  RV_CFLAGS       := -march=rv64i -mabi=lp64
else
  RV_TARGET_FLAGS :=
  # Ensure the first PT_LOAD segment starts at 0x80000000
  RV_LDFLAGS      := -nostartfiles -nostdlib -static -Wl,-Ttext-segment=0x80000000 -Wl,--no-relax
  RV_CFLAGS       := -march=rv64i -mabi=lp64
endif

# Optional: limit steps when tracing (0 = unlimited)
STEPS ?= 0

.PHONY: all clean run

all: rv64emu x1_set.elf

# Build the emulator (native)
rv64emu: rv64emu.c
	$(CC) $(CFLAGS) $< -o $@

# Build minimal ELF that writes x1 and exits via ecall
x1_set.elf: x1_set.S
	@command -v $(RV_CC) >/dev/null || { \
	  echo "Error: $(RV_CC) not found. Install riscv64-unknown-elf-gcc or set RV_CC=clang (with lld)."; \
	  exit 1; \
	}
	$(RV_CC) $(RV_TARGET_FLAGS) $(RV_CFLAGS) $(RV_LDFLAGS) $< -o $@

# Run with trace so registers print each step
run: all
	./rv64emu -i x1_set.elf --trace $(if $(filter-out 0,$(STEPS)),--steps $(STEPS),)

clean:
	rm -f rv64emu x1_set.elf
