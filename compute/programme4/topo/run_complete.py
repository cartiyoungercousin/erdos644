import itertools, sys, time
from toy_complex import report
k = int(sys.argv[1])
for n in map(int, sys.argv[2:]):
    t = time.time()
    report(f"K^({k})_{n}", [set(e) for e in itertools.combinations(range(n), k)])
    print("  secs", round(time.time() - t, 1), flush=True)
