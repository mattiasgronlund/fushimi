source scripts/common.sh
run inari-b5dd856 b5dd856-aarch64-r4 --bench primitives --bench intervals -- '^[^t]'
run inari-asin-7e92e46 7e92e46-aarch64-r4 --bench primitives --bench intervals -- '^[^t]'
echo B4-done
