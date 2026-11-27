#!/usr/bin/env bash
# Install elan and the pinned Lean toolchain for a Lake package directory,
# using authenticated GitHub downloads and retries to avoid transient 403s.
set -euo pipefail

if (( $# != 1 )); then
  echo "usage: $0 <lake-package-dir>" >&2
  exit 2
fi

pkg_dir=$1
if [[ ! -f "$pkg_dir/lean-toolchain" ]]; then
  echo "ERROR: missing $pkg_dir/lean-toolchain" >&2
  exit 1
fi

tmp_dir=""
cleanup() {
  if [[ -n "$tmp_dir" ]]; then
    rm -rf -- "$tmp_dir"
  fi
}
trap cleanup EXIT

retry() {
  local max_attempts=$1
  shift
  local attempt=1
  local delay=5
  while true; do
    if "$@"; then
      return 0
    fi
    if (( attempt >= max_attempts )); then
      return 1
    fi
    echo "Attempt $attempt/$max_attempts failed; retrying in ${delay}s..." >&2
    sleep "$delay"
    attempt=$((attempt + 1))
    delay=$((delay * 2))
  done
}

install_elan() {
  local arch target archive
  arch=$(uname -m)
  case "$arch" in
    x86_64 | amd64)
      target="x86_64-unknown-linux-gnu"
      ;;
    aarch64 | arm64)
      target="aarch64-unknown-linux-gnu"
      ;;
    *)
      echo "ERROR: unsupported Linux architecture: $arch" >&2
      return 1
      ;;
  esac

  tmp_dir=$(mktemp -d)
  archive="$tmp_dir/elan-${target}.tar.gz"

  download_archive() {
    rm -f "$archive"
    if [[ -n "${GH_TOKEN:-}" ]] && command -v gh >/dev/null 2>&1; then
      gh release download \
        --repo leanprover/elan \
        --pattern "elan-${target}.tar.gz" \
        --dir "$tmp_dir"
    else
      curl -fsSL \
        "https://github.com/leanprover/elan/releases/latest/download/elan-${target}.tar.gz" \
        -o "$archive"
    fi
  }

  retry 5 download_archive
  tar -xzf "$archive" -C "$tmp_dir"
  "$tmp_dir/elan-init" -y --default-toolchain none --no-modify-path
}

if ! command -v elan >/dev/null 2>&1 && [[ ! -x "$HOME/.elan/bin/elan" ]]; then
  install_elan
fi

export PATH="$HOME/.elan/bin:$PATH"
if [[ -n "${GITHUB_PATH:-}" ]]; then
  echo "$HOME/.elan/bin" >>"$GITHUB_PATH"
fi

cd "$pkg_dir"
retry 5 lean --version
lake --version
