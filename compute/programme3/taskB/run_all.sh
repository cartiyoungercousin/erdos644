#!/bin/sh
# 4 processes, ~22 minutes each
cd "$(dirname "$0")"
(py -3.14 taskb.py 8 7 16 random 1 10 > out/log_8_7_16_a.txt 2>&1; py -3.14 taskb.py 8 7 16 layer=X:8:1 1 10 >> out/log_8_7_16_a.txt 2>&1) &
(py -3.14 taskb.py 8 7 16 randlayer=2 2 10 > out/log_8_7_16_b.txt 2>&1; py -3.14 taskb.py 8 7 16 random 2 10 >> out/log_8_7_16_b.txt 2>&1) &
py -3.14 taskb.py 10 8 21 random 1 20 > out/log_10_8_21_random.txt 2>&1 &
py -3.14 taskb.py 10 8 21 layer=X:12:1 1 20 > out/log_10_8_21_layer.txt 2>&1 &
wait
