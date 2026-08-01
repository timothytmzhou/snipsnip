#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
dist_dir="$repo_root/dist"
wasm_input="$repo_root/target/wasm32-unknown-unknown/release/prefixspace_web.wasm"

if ! command -v wasm-bindgen >/dev/null 2>&1; then
  echo "wasm-bindgen-cli is required (expected version 0.2.126)" >&2
  exit 1
fi

cargo build \
  --manifest-path "$repo_root/Cargo.toml" \
  --package prefixspace-web \
  --release \
  --target wasm32-unknown-unknown

mkdir -p "$dist_dir/pkg"
cp -R "$repo_root/web/site/." "$dist_dir/"
wasm-bindgen \
  "$wasm_input" \
  --target web \
  --out-dir "$dist_dir/pkg" \
  --out-name snipsnip_demo \
  --no-typescript

touch "$dist_dir/.nojekyll"
