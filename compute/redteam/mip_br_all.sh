for a in U O; do for b in U O; do for c in U O; do for d in U O; do for e in U O; do for f in U O; do
 timeout 1200 py mip_br.py $a$b$c$d$e$f 600 0.5 2>&1 | grep -E "status|MILP|EXACT"
done; done; done; done; done; done
