#!/bin/bash
# CORE 112 batch: profile-family searches. Usage: bash batch.sh k T n q [nondeg]  -> logs/batch_k_T_n_q.log
cd "$(dirname "$0")"; export PYTHONIOENCODING=utf-8
k=$1; T=$2; n=$3; q=$4; nd=${5:-x}; out=logs/batch_${k}_${T}_${n}_q${q}_${nd}.log; : > $out
py -3.14 - "$n" "$q" <<'PY' > logs/parts_${k}_${T}_${n}_q${q}.txt
import sys
n, q = int(sys.argv[1]), int(sys.argv[2])
def parts(n, q, mx):
    if q == 1:
        if 1 <= n <= mx: yield (n,)
        return
    for a in range(min(n - q + 1, mx), 0, -1):
        for r in parts(n - a, q - 1, a): yield (a,) + r
for p in parts(n, q, n): print(",".join(map(str, p)))
PY
while read cells; do timeout 2700 py -3.14 profile_search.py $k $T $n $cells $nd b >> $out 2>&1 || echo "k=$k T=$T n=$n cells=$cells: ERROR/TIMEOUT" >> $out; done < logs/parts_${k}_${T}_${n}_q${q}.txt
echo BATCH_DONE >> $out
