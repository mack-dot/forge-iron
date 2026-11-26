#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
ASM_CAKE="$ROOT/kernel/hol4/counter_arm8.S"
ASM_SHIM="$ROOT/kernel/shim/shim.S"
LD_SCRIPT="$ROOT/kernel/shim/forge.ld"
OUT_DIR="$ROOT/kernel/build"
OUT_BIN="$OUT_DIR/forge-kernel"
OUT_HASH="$OUT_DIR/machine_bytes_hash.txt"

mkdir -p "$OUT_DIR"

if [ ! -f "$ASM_CAKE" ]; then
  echo "error: missing $ASM_CAKE (run Holmake first)" >&2
  exit 1
fi

ASM_CAKE_PP="$OUT_DIR/counter_arm8.s"
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
  "$AS_BIN" -o "$OUT_DIR/counter_arm8.o" "$ASM_CAKE_PP"
  "$AS_BIN" -o "$OUT_DIR/shim.o" "$ASM_SHIM"
  "$LD_BIN" --build-id=none -static -nostdlib -T "$LD_SCRIPT" \
    -o "$OUT_BIN" "$OUT_DIR/counter_arm8.o" "$OUT_DIR/shim.o"
}

if [ "$(uname -s)" = "Linux" ] && [ "$(uname -m)" = "aarch64" ]; then
  run_link as ld
elif command -v aarch64-linux-gnu-as >/dev/null 2>&1 && command -v aarch64-linux-gnu-ld >/dev/null 2>&1; then
  run_link aarch64-linux-gnu-as aarch64-linux-gnu-ld
else
  DOCKER_IMG="${FORGE_ARM64_DOCKER_IMAGE:-forge-arm64-tools:bookworm}"
  docker run --rm -v "$ROOT:/repo" "$DOCKER_IMG" sh -eu -c '
    as -o /repo/kernel/build/counter_arm8.o /repo/kernel/build/counter_arm8.s
    as -o /repo/kernel/build/shim.o /repo/kernel/shim/shim.S
    ld --build-id=none -static -nostdlib -T /repo/kernel/shim/forge.ld \
      -o /repo/kernel/build/forge-kernel /repo/kernel/build/counter_arm8.o /repo/kernel/build/shim.o
  '
fi

python3 -c '
import hashlib, pathlib, sys
p = pathlib.Path(sys.argv[1])
h = hashlib.sha256(p.read_bytes()).hexdigest()
pathlib.Path(sys.argv[2]).write_text(h + "\n")
print(f"built {p} ({p.stat().st_size} bytes) sha256={h}")
' "$OUT_BIN" "$OUT_HASH"
