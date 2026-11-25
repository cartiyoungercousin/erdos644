r"""Experiments for Task 3.  Usage: py -3.14 run.py <suite> <seed> <count>
suites: parity (q-cell parity families, optional free cell), random (random codes of codimension 1..4).
For each instance (n, k with 0 <= 4n-7k):
  Wany  = min W over disjoint Omega_i in a+C (any parity)        -> literal hypothesis of Prop. 9
  Wk    = min W with every |Omega_i| = k mod 2                    -> hypothesis of Theorem 9'
  cons  = result of the triangle construction (verified EXACTLY)
  ilp   = ground truth (count ILP; positive answers verified EXACTLY)
Writes one JSON line per instance."""
import sys, json, random, time
from core import *
from construct import construct
from ilp import good_seven_counts, sets_from_counts, min_triple

def parity_family(sizes, free=0):
    n = sum(sizes) + free; rows = []; o = 0
    for s in sizes: rows.append(((1 << s) - 1) << o); o += s
    return Coset(n, rows, (1 << len(sizes)) - 1, f'parity{sizes}+free{free}')

def random_code(n, r, rng):
    while True:
        rows = [rng.getrandbits(n) for _ in range(r)]
        if rank(rows) == r: break
    return Coset(n, rows, rng.randrange(1, 1 << r), f'random n={n} r={r}')

def h_nonempty(cells, alpha, k):
    st = {(0, 0)}
    for g, N in cells.items():
        st = {(a + c, b ^ (g if c & 1 else 0)) for (a, b) in st for c in range(N + 1) if a + c <= k}
    return (k, alpha) in st

def restrict_live(cs, k):
    """Delete the points lying in no member of H (the notes take V = union of H)."""
    ce = evenise(cs, k); cells = {g: len(v) for g, v in ce.cells().items()}
    live = []
    for x in range(cs.n):
        g = ce.cls(x); c2 = dict(cells); c2[g] -= 1
        if c2[g] == 0: del c2[g]
        if h_nonempty(c2, ce.alpha ^ g, k - 1): live.append(x)
    if len(live) == cs.n: return cs
    rows = [sum(((h >> x) & 1) << i for i, x in enumerate(live)) for h in cs.H]
    return Coset(len(live), rows, cs.alpha, cs.name + f' [live {len(live)}/{cs.n}]')

def instance(cs, k, sat_n=20):
    t0 = time.time()
    cs = restrict_live(cs, k)
    rec = dict(name=cs.name, n=cs.n, k=k, slack=4 * cs.n - 7 * k, r=cs.r, H=cs.H, alpha=cs.alpha)
    ce = evenise(cs, k)
    rec['even'] = cs.is_even()
    rec['H_nonempty'] = h_nonempty({g: len(v) for g, v in ce.cells().items()}, ce.alpha, k)
    if not rec['H_nonempty']: return rec
    Wany, _ = min_triple(cs)
    Wk, Os = min_triple(ce)
    rec['Wany'], rec['Wk'] = Wany, Wk
    rec['hyp_literal'] = Wany is not None and Wany <= rec['slack']
    rec['hyp_k'] = Wk is not None and Wk <= rec['slack']
    if rec['hyp_k']:
        B, info = construct(ce, k, Os)
        rec['cons'] = 'ok' if B and verify_seven(cs, k, B)[0] else ('VERIFY-FAIL' if B else info)
        if B: rec['cons_info'] = {a: b for a, b in info.items() if a in ('W', 's', 'f', 'u', 'm', 'strictH4')}
        B2, info2 = construct(ce, k, Os, brief=True)
        rec['cons_brief'] = 'ok' if B2 and verify_seven(cs, k, B2)[0] else ('VERIFY-FAIL' if B2 else info2)
        from ystep_ilp import construct_ilp
        B3, info3 = construct_ilp(ce, k, Os, brief=True)
        rec['cons_ilp'] = 'ok' if B3 and verify_seven(cs, k, B3)[0] else ('VERIFY-FAIL' if B3 else info3)
    cells = {g: len(v) for g, v in ce.cells().items()}
    rec['cells'] = sorted(cells.values(), reverse=True)
    zc, st = good_seven_counts(cells, ce.alpha, ce.r, k)
    if zc:
        ok, why = verify_seven(cs, k, sets_from_counts(ce, zc))
        rec['ilp'] = 'good' if ok else 'VERIFY-FAIL ' + why
    else:
        rec['ilp'] = 'none:' + st
        if (rec['hyp_literal'] or rec['hyp_k']) and cs.n <= sat_n:
            from sat_check import good_seven_sat
            rec['sat_fano'] = good_seven_sat(cs, k, 'fano')[0]
            rec['sat_any'] = good_seven_sat(cs, k, 'any')[0]
    rec['sec'] = round(time.time() - t0, 2)
    return rec

def ks(n, lo=3):
    return [k for k in range(lo, n) if 4 * n - 7 * k >= 0 and 4 * n - 7 * k <= 24]

if __name__ == '__main__':
    suite, seed, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    out = open(f'logs/{suite}_{seed}.jsonl', 'w')
    for it in range(count):
        if suite == 'parity':
            q = rng.choice([2, 3, 4]); sizes = [rng.randint(2, 7) for _ in range(q)]
            free = rng.choice([0, 0, 1, 2, 3])
            cs = parity_family(sizes, free)
        elif suite == 'large':
            if rng.random() < 0.5:
                q = rng.choice([2, 3, 4, 5]); sizes = [rng.randint(5, 30) for _ in range(q)]
                cs = parity_family(sizes, rng.choice([0, 0, 1, 3, 5]))
            else:
                cs = random_code(rng.randint(30, 80), rng.choice([2, 3, 4]), rng)
        elif suite == 'fkw':
            m = it + 2; cs = Coset(7 * m + 2, [(1 << 4 * m) - 1, ((1 << 3 * m + 2) - 1) << 4 * m], 3, f'FKW+1 m={m}')
        else:
            n = rng.randint(9, 20); r = rng.choice([1, 2, 3, 4])
            cs = random_code(n, r, rng)
        for k in ([4 * (it + 2)] if suite == 'fkw' else ks(cs.n, lo=3) if suite != 'large' else [k for k in ks(cs.n) if 4 * cs.n - 7 * k <= 24][-3:]):
            rec = instance(cs, k)
            if not rec['H_nonempty'] or 4 * rec['n'] - 7 * k < 0: continue
            out.write(json.dumps(rec) + '\n'); out.flush()
            flag = ''
            if rec['hyp_literal'] and not rec['ilp'].startswith('good'): flag += ' <<LITERAL-FAILS>>'
            if rec['hyp_k'] and not rec['ilp'].startswith('good'): flag += ' <<HYPK-FAILS>>'
            if 'FAIL' in str(rec.get('cons', '')) or 'FAIL' in rec['ilp']: flag += ' <<VERIFY>>'
            print(rec['name'], 'k', k, 'sl', rec['slack'], 'Wany', rec['Wany'], 'Wk', rec['Wk'], 'cons', rec.get('cons'), rec.get('cons_brief'), rec.get('cons_ilp'), 'ilp', rec['ilp'], rec.get('sat_fano'), rec.get('sat_any'), rec['sec'], flag, flush=True)
