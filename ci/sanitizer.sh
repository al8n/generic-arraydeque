#!/usr/bin/env bash

set -euo pipefail

TARGET="${SANITIZER_TARGET:-x86_64-unknown-linux-gnu}"
FEATURES="${SANITIZER_FEATURES:-unstable}"
COMMON_TEST_ARGS=(--features "${FEATURES}")

# Keep ODR detection disabled (match stdlib) but allow leak detection so we do
# not need a dedicated LSan stage.
export ASAN_OPTIONS="${ASAN_OPTIONS:-detect_odr_violation=0:detect_leaks=1}"

echo "==> AddressSanitizer: unit/integration/examples/bench tests (${TARGET})"
RUSTFLAGS="-Z sanitizer=address" \
  cargo test --target "${TARGET}" --all-targets "${COMMON_TEST_ARGS[@]}"
