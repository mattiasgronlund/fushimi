source scripts/common.sh
run inari-b5dd856 b5dd856-generic-r4 --features force-generic --bench primitives --bench intervals -- '^[^t]'
run inari-asin-7e92e46 7e92e46-generic-r4 --features force-generic --bench primitives --bench intervals -- '^[^t]'
echo B5-done
