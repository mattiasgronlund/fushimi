source scripts/common.sh
cb inari-b5dd856 --no-run --bench primitives --bench intervals > out/build-b-b5dd856-aarch64.txt 2>&1
cb inari-b5dd856 --no-run --features force-generic --bench primitives --bench intervals > out/build-b-b5dd856-generic.txt 2>&1
cb inari-asin-7e92e46 --no-run --bench primitives --bench intervals > out/build-b-7e92e46-aarch64.txt 2>&1
cb inari-asin-7e92e46 --no-run --features force-generic --bench primitives --bench intervals > out/build-b-7e92e46-generic.txt 2>&1
sleep 60
for k in $(echo ${ROUNDS:-1 2}); do
  run inari-b5dd856 "b5dd856-aarch64-r$k" --bench primitives --bench intervals -- '^[^t]'
  run inari-b5dd856 "b5dd856-generic-r$k" --features force-generic --bench primitives --bench intervals -- '^[^t]'
  run inari-asin-7e92e46 "7e92e46-aarch64-r$k" --bench primitives --bench intervals -- '^[^t]'
  run inari-asin-7e92e46 "7e92e46-generic-r$k" --features force-generic --bench primitives --bench intervals -- '^[^t]'
done
[ -n "$TOKEN" ] && run inari-asin-7e92e46 7e92e46-token-r1 --bench intervals -- '^token/'
echo B-done
