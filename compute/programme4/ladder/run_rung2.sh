#!/bin/bash
# Kaggle driver: four Rung 2 orbit CEGAR runs in parallel (one core each).
export NODE_LIMIT=200000000
timeout 8500 python orbit_cegar.py agl1_19 19 9 8 1000000 js > out_agl1_19.txt 2>&1 &
timeout 8500 python orbit_cegar.py psl3_4 21 10 9 1000000 js > out_psl3_4.txt 2>&1 &
timeout 8500 python orbit_cegar.py agl2_5 25 13 10 10000000 heur > out_agl2_5.txt 2>&1 &
timeout 8500 python orbit_cegar.py psl2_25 26 14 10 10000000 heur > out_psl2_25.txt 2>&1 &
wait
