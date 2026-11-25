#!/bin/sh
# runs jobs.txt with 2 parallel workers, 240 s cap each
cd "$(dirname "$0")"
awk '{print $1, $2, $3, $4, $5}' jobs.txt | xargs -P 2 -L 1 sh -c 'echo "[$4] $(py -3.14 pen_sat.py $0 $1 $2 $3 240 | head -1)"' > logs/pen_sat_sweep.log 2>&1
