source scripts/common.sh
for k in 4 5; do
  run inari-asin-7e92e46 "asin-7e92e46-r$k" --bench asin_acos --
  run inari-asin-daa51d1 "asin-daa51d1-r$k" --bench asin_acos --
done
echo A2-done
