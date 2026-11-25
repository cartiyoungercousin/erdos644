#!/bin/sh
# 7INV panel (<= 4 parallel jobs). Output: logs/panel_*.log.  Run from this directory.
export PYTHONPATH=../seven
r() { py -3.14 analyse.py "$1" "$2" 1 > "logs/panel_$3.log" 2>&1; }
r fkw:3 200000 fkw3 &
r taskb:sa_10_8_21_random_s1.npy:21:10 200000 tb21r &
r taskb:sa_10_8_21_layer_X_12_1_s1.npy:21:10 200000 tb21l &
r covrand:21:10:3:1 200000 cr21 &
wait
r covrand:20:10:2:1 200000 cr20 &
r coset:21:10:3:1 200000 cs21_3 &
r coset:21:10:4:1 200000 cs21_4 &
r coset:21:10:5:1 200000 cs21_5 &
wait
r quad:21:12:1 200000 q21_12 &
r quad:22:12:1 200000 q22_12 &
r quad:20:10:1 200000 q20_10 &
r mod4:21:12:12:1 200000 m4_21 &
wait
r mod4:22:12:12:1 200000 m4_22 &
r thresh:23:12:21:12 200000 thr23 &
r star:21:10:3:1 200000 star21 &
r quad:23:12:1 200000 q23_12 &
wait
