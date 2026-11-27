#!/usr/bin/env bash
# Generic Forge Runtime Static AArch64 ELF Builder (256 KB Code Slot, _start = 0x450000)
# Usage:
#   runtime/shim/build_elf.sh <cake_asm.S> <16|64> <out_dir>
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ASM_CAKE="${1:-$ROOT/kernels/counter/hol4/counter_arm8.S}"
FRAME_SIZE="${2:-16}"
OUT_DIR="${3:-$ROOT/kernels/counter/build}"

if [ "$FRAME_SIZE" = "16" ]; then
  ASM_SHIM="$ROOT/runtime/shim/shim16.S"
elif [ "$FRAME_SIZE" = "64" ]; then
  ASM_SHIM="$ROOT/runtime/shim/shim64.S"
else
  echo "error: unsupported frame size '$FRAME_SIZE' (expected 16 or 64)" >&2
  exit 1
fi

LD_SCRIPT="$ROOT/runtime/shim/forge_slot.ld"
OUT_BIN="$OUT_DIR/forge-kernel"
OUT_HASH="$OUT_DIR/machine_bytes_hash.txt"

mkdir -p "$OUT_DIR"

if [ ! -f "$ASM_CAKE" ]; then
  echo "error: missing $ASM_CAKE (run Holmake first)" >&2
  exit 1
fi

ASM_CAKE_PP="$OUT_DIR/cake_pp.s"
if command -v cc >/dev/null 2>&1; then
  cc -E -P -U__APPLE__ -U__MACH__ -D__ELF__ -x assembler-with-cpp "$ASM_CAKE" -o "$ASM_CAKE_PP"
elif command -v cpp >/dev/null 2>&1; then
  cpp -P -U__APPLE__ -U__MACH__ -D__ELF__ "$ASM_CAKE" -o "$ASM_CAKE_PP"
else
  echo "error: need cc or cpp to preprocess $ASM_CAKE" >&2
  exit 1
fi

run_link() {
  local AS_BIN="$1"
  local LD_BIN="$2"
  "$AS_BIN" -o "$OUT_DIR/cake.o" "$ASM_CAKE_PP"
  "$AS_BIN" -o "$OUT_DIR/shim.o" "$ASM_SHIM"
  "$LD_BIN" --build-id=none -static -nostdlib -T "$LD_SCRIPT" \
    -o "$OUT_BIN" "$OUT_DIR/cake.o" "$OUT_DIR/shim.o"
}

if [ "$(uname -s)" = "Linux" ] && [ "$(uname -m)" = "aarch64" ]; then
  run_link as ld
elif command -v aarch64-linux-gnu-as >/dev/null 2>&1 && command -v aarch64-linux-gnu-ld >/dev/null 2>&1; then
  run_link aarch64-linux-gnu-as aarch64-linux-gnu-ld
else
  DOCKER_IMG="${FORGE_ARM64_DOCKER_IMAGE:-forge-arm64-tools:bookworm}"
  REL_PP="${ASM_CAKE_PP#$ROOT/}"
  REL_SHIM="${ASM_SHIM#$ROOT/}"
  REL_OUT="${OUT_DIR#$ROOT/}"
  docker run --rm -v "$ROOT:/repo" "$DOCKER_IMG" sh -eu -c "
    as -o /repo/$REL_OUT/cake.o /repo/$REL_PP
    as -o /repo/$REL_OUT/shim.o /repo/$REL_SHIM
    ld --build-id=none -static -nostdlib -T /repo/runtime/shim/forge_slot.ld \
      -o /repo/$REL_OUT/forge-kernel /repo/$REL_OUT/cake.o /repo/$REL_OUT/shim.o
  "
fi

rm -f "$OUT_DIR/cake.o" "$OUT_DIR/shim.o" "$ASM_CAKE_PP"

python3 -c '
import hashlib, pathlib, sys
p = pathlib.Path(sys.argv[1])
h = hashlib.sha256(p.read_bytes()).hexdigest()
pathlib.Path(sys.argv[2]).write_text(h + "\n")
print(f"built {p} ({p.stat().st_size} bytes) sha256={h}")
' "$OUT_BIN" "$OUT_HASH"
