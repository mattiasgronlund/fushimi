source scripts/common.sh
cb inari-asin-7e92e46 --no-run --bench asin_acos > out/build-a-7e92e46.txt 2>&1
cb inari-asin-daa51d1 --no-run --bench asin_acos > out/build-a-daa51d1.txt 2>&1
sleep 60
for k in 1 2 3; do
  run inari-asin-7e92e46 "asin-7e92e46-r$k" --bench asin_acos --
  run inari-asin-daa51d1 "asin-daa51d1-r$k" --bench asin_acos --
done
echo A-done
