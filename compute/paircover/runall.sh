#!/bin/sh
# CORE 117: paircover.py (LP + SAT for the integral rho) on every stored T-covering family (T = 6), 12 in parallel
cd "$(dirname "$0")"
cat famlist_sat.txt | xargs -P 12 -I{} sh -c 'b=$(basename {} .txt); py -3.14 -u paircover.py {} 6 - 2400 > logs/pc_$b.log 2>&1'
