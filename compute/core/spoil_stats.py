"""which menu dumps spoil?  statistics along self-play (CORE Part IX)"""
import sys, json, random, collections
import spoil as SP
t, N, o, seed, depth, ncand = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
E = SP.Engine(t, N); rng = random.Random(seed); c = N - 1
m = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}; nrep = 2
while nrep < depth:
    cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); cs = cs[:ncand]
    target = min(vold, E.base); rows = []
    stat = collections.Counter(); mins = []
    for s in cs:
        v, d, sp = E.score(m, nrep, s, target, all_spoilers=True)
        menu = E.menu(m, s)
        pure = [d for d in menu if len([1 for x in d.values() if x > 1e-9]) == 1]
        spk = {tuple(sorted(d.items())) for d in sp}
        for d in pure:
            J = [J for J, x in d.items() if x > 1e-9][0]
            stat[(SP.popc(J), tuple(sorted(d.items())) in spk)] += 1
        mins.append((len(sp), len(menu), sum(1 for d in pure if tuple(sorted(d.items())) in spk), len(pure)))
        if sp: rows.append((s, sp))
    mins.sort()
    print(json.dumps(dict(nrep=nrep, ncells=len(m), vold=vold, fewest_spoilers=mins[:6], pure_by_codeg={f"{k[0]}{'S' if k[1] else 'x'}": v for k, v in sorted(stat.items())})), flush=True)
    if not rows: print("NO SPOILER for all"); break
    s, sp = rng.choice(rows); d = rng.choice(sp)
    m = E.step(m, s, d, 1 << nrep); nrep += 1
