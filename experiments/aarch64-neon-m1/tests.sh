#!/bin/zsh
TOP=/Users/mattias/git/mattiasgronlund
O=$TOP/out6/tests
mkdir -p $O
export CARGO_BUILD_JOBS=5 RUST_TEST_THREADS=5
cd $TOP/inari-neon
cargo test --release > $O/neon-test-release.txt 2>&1; echo "neon release exit $?"
cargo test --release --features force-generic > $O/neon-test-release-force-generic.txt 2>&1; echo "neon generic exit $?"
INARI_DIFF_N=10000000 cargo test --release --lib simd::differential_tests -- --nocapture > $O/neon-diff-10M.txt 2>&1; echo "neon diff10M exit $?"
cargo test --release --lib simd::differential_tests -- --nocapture > $O/neon-diff-default.txt 2>&1; echo "neon diff exit $?"
for v in V1 V24 V6s V246s; do
  cd $TOP/inari-$v
  CARGO_TARGET_DIR="$TOP/target-vtest" cargo test --release --lib simd::differential_tests -- --nocapture > $O/$v-diff-default.txt 2>&1; echo "$v diff exit $?"
done
echo ALLDONE
