"""Random tau-critical families: test the toy criterion at tau = target.
usage: run_random.py k n target trials seed"""
import itertools, random, sys, time
from toy_complex import report, tau
k, n, target, trials, seed = map(int, sys.argv[1:6])
rng = random.Random(seed)
allk = [frozenset(e) for e in itertools.combinations(range(n), k)]
for t in range(trials):
    fam = list(allk); rng.shuffle(fam)
    if tau(fam) < target:
        print("complete family tau too small"); break
    # delete members greedily while tau >= target  -> tau-critical at >= target
    i = 0
    while i < len(fam):
        trial = fam[:i] + fam[i+1:]
        if tau(trial) >= target:
            fam = trial
        else:
            i += 1
    t0 = time.time()
    report(f"rand k{k} n{n} s{seed}.{t}", fam)
    print("   members:", [''.join(map(str, sorted(B))) for B in fam], round(time.time()-t0, 1), "s", flush=True)
