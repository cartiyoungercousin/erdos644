# Good-seven finder for stored families + exact verification (no transversal of size <= 2, brute force).
# Pattern search: assign each point a co-type from a seven-type M (minimal co-types); member i must fit in
# R_i = {x : i not in cotype(x)}. Hill-climb on #satisfied i. Patterns tried: Fano (7/4), the four 11/6 types.
import sys, json, itertools, random
import numpy as np
rows = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'programme2', 'verify', 'out', 'maxint7_classes_lp.json')))
def parse(hx):
    v = int(hx, 16); return [g for g in range(128) if v >> g & 1]
def minimal(M):
    S = set(M); return [F for F in M if not any((F & ~(1 << i)) in S for i in range(7) if F >> i & 1)]
pats = [(r['lp'], minimal(parse(r['mask']))) for r in rows if r['lp'] in ('7/4', '11/6', '15/8')]
pats.sort(key=lambda p: {'7/4': 0, '11/6': 1, '15/8': 2}[p[0]])

def load(path, n):
    full = (1 << n) - 1
    return np.array([full ^ int(x) for x in open(path).read().split()], dtype=np.int64)

def sat_members(mem, n, cot):
    out = []
    for i in range(7):
        R = 0
        for x in range(n):
            if not cot[x] >> i & 1: R |= 1 << x
        hit = np.nonzero((mem & ~np.int64(R)) == 0)[0]
        out.append(int(mem[hit[0]]) if len(hit) else None)
    return out

def score(mem, n, cot):
    s = 0
    for i in range(7):
        R = 0
        for x in range(n):
            if not cot[x] >> i & 1: R |= 1 << x
        s += bool(np.any((mem & ~np.int64(R)) == 0))
    return s

def verify(sev, n):
    for x in range(n):
        for y in range(x, n):
            m = (1 << x) | (1 << y)
            if all(B & m for B in sev): return False
    return True

def search(mem, n, cots, rng, sweeps=40):
    cot = [rng.choice(cots) for _ in range(n)]
    s = score(mem, n, cot)
    for _ in range(sweeps):
        improved = False
        for x in rng.sample(range(n), n):
            old = cot[x]; best = (s, old)
            for F in cots:
                if F == old: continue
                cot[x] = F; v = score(mem, n, cot)
                if v > best[0] or (v == best[0] and rng.random() < 0.3): best = (v, F)
            cot[x] = best[1]; improved |= best[0] > s; s = best[0]
            if s == 7: return cot
        if not improved and rng.random() < 0.5:
            for x in rng.sample(range(n), 3): cot[x] = rng.choice(cots)
            s = score(mem, n, cot)
    return None

if __name__ == '__main__':
    path, n, tries = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    mem = load(path, n); rng = random.Random(1)
    print(path.split('/')[-1], 'members', len(mem), 'k', bin(int(mem[0])).count('1'), flush=True)
    for lp, cots in pats[:5]:
        for t in range(tries):
            cot = search(mem, n, cots, rng)
            if cot:
                sev = sat_members(mem, n, cot)
                ok = verify(sev, n)
                print(f'  FOUND type LP={lp} try {t}: seven verified no-2-cover={ok}; members(hex)=', [hex(b) for b in sev], flush=True)
                if ok: sys.exit(0)
        print(f'  type LP={lp}: none in {tries} tries', flush=True)
