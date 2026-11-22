#!/usr/bin/env bash
set -eu

cd $(dirname $0)/..

# ITF1788's plugin (rust, inari, inari) writes `use inari::`, and this script does not change
# that line: rename it to `use fushimi::` by hand in the files it writes to tests/itf1788_tests/.
tmp_dir=$(mktemp -d)
PYTHONPATH=ITF1788 python3 -m itf1788 -c '(rust, inari, inari)' -s ITF1788/itl -o $tmp_dir
for f in $tmp_dir/rust/inari/inari/*
do
    b=$(basename "$f")
    mv "$f" tests/itf1788_tests/$(echo "$b" | tr '-' '_')
done
