cd /c/Users/USER/lean644/compute/petal4
while pgrep -f "run2.sh" >/dev/null || pgrep -f "search.py 12 6" >/dev/null; do sleep 5; done
py search.py 16 4 28 44 7198 1750 > logs/k16_m4_n28_44_resume.log 2>&1
