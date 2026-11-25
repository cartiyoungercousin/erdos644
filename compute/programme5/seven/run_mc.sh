#!/bin/sh
# Monte Carlo panel (6 parallel jobs max). Output: logs/mc_*.log
D=../../programme3/taskB/out
run() { py -3.14 mc_colour.py "$1" "$2" 1 > "logs/mc_$3.log" 2>&1; }
run file:$D/sa_8_7_16_random_s1.npy:16:8 400000 tb8r &
run file:$D/sa_8_7_16_layer_X_8_1_s1.npy:16:8 400000 tb8l &
run file:$D/sa_10_8_21_random_s1.npy:21:10 400000 tb10r &
run file:$D/sa_10_8_21_layer_X_12_1_s1.npy:21:10 400000 tb10l &
run file:$D/sa_12_10_23_random_s1.npy:23:12 200000 tb12r &
run file:$D/sa_12_10_23_layer_X_12_1_s1.npy:23:12 200000 tb12l &
wait
run fkw:3 200000 fkw3 &
run fkw:4 200000 fkw4 &
run fkw:5 200000 fkw5 &
run complete:20:12 200000 K20_12 &
run thresh:23:12:21:12 200000 thr23 &
run covrand:21:10:3:1 200000 cr21 &
wait
run covrand:22:12:2:1 200000 cr22 &
run covrand:20:10:2:1 200000 cr20 &
run thresh:29:16:28:16 200000 thr29 &
wait
