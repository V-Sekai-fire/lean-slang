#!/usr/bin/env bash
# Fetch the Slang SDK (headers + libs) into vendor/ for the libslang FFI.
# The binaries are gitignored; run this once before `lake build slangcheck`.
set -euo pipefail
VER="${SLANG_VERSION:-2026.11}"
URL="https://github.com/shader-slang/slang/releases/download/v${VER}/slang-${VER}-linux-x86_64-glibc-2.28.tar.gz"
DIR="$(cd "$(dirname "$0")" && pwd)"
echo "fetching Slang ${VER} → ${DIR}"
tmp="$(mktemp -d)"
curl -fsSL "$URL" -o "$tmp/slang.tar.gz"
tar xzf "$tmp/slang.tar.gz" -C "$tmp"
rm -rf "$DIR/include" "$DIR/lib"
cp -r "$tmp/include" "$DIR/include"
cp -r "$tmp/lib"     "$DIR/lib"
rm -rf "$tmp"
echo "done: $(ls "$DIR/lib/libslang.so" "$DIR/include/slang.h")"
