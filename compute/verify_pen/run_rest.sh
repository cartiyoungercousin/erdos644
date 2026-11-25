#!/bin/sh
# remaining [C] instances at n=13 (glucose4: supports interrupt), 2 workers
cd "$(dirname "$0")"
export PEN_SOLVER=g4
printf '13 6 1 2 C\n13 7 1 1 C\n13 6 2 4 C\n12 5 2 1 Csharp\n' | xargs -P 2 -L 1 sh -c 'echo "[$4] $(py -3.14 pen_sat.py $0 $1 $2 $3 240 | head -1)"' >> logs/pen_sat_sweep.log 2>&1
