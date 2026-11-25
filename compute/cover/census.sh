#!/bin/sh
# CORE 106 census: (Σ)(a),(b) counts by certs_lean.py, good seven by ../core9/seven_dfs.js (n=15,16) or seven_sat.py (n=17)
# (n = 15 sum/code families, 3000+ members with r = 1 or 7 of 15 residues, are skipped: Q' count too slow, and not informative)
for f in $(ls logs/d_8_6_*_*.txt logs/c1_8_6_1[67]_s1.txt | grep -v -e 15_code -e 15_sum); do
  n=$(echo $f | sed 's/.*_8_6_\([0-9]*\)_.*/\1/')
  echo "=== $f"
  py -3.14 certs_lean.py 8 6 $n $f 2>&1 | sed -n 1,3p
  if [ $n -le 16 ]; then node ../core9/seven_dfs.js $f $n | tail -2; else py -3.14 seven_sat.py $f $n; fi
done
