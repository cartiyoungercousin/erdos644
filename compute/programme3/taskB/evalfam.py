r"""Post-hoc evaluation for Task B.  For each SA result json: rebuild the start family (deterministic), load the final
family (.npy), and evaluate both on a large independent colouring panel (seven measures with standard errors), plus the
structure measures.  Also a noise reference: uniformly random subfamilies of the complete layer with the same size
(not covering), to calibrate prop1/prop2/Fourier maxima.  [heuristic: Monte Carlo for the seven measures]
usage: evalfam.py result.json [Pbig]"""
import sys, os, json, random
import numpy as np
from taskb import State, Panel, measures, ksets, fwht, planted_layer, pc, find_layers

def big_stats(members, n, c, P, seed, chunk=200000):
    rng = np.random.default_rng(seed); prods = []; certs = []; tried = 0
    g = np.zeros(1 << n, np.int32); g[members] = 1
    from taskb import zeta_sub
    g = zeta_sub(g, n); full = (1 << n) - 1
    done = 0
    while done < P:
        pan = Panel(n, c, min(chunk, P - done), rng); N = g[full ^ pan.Lm].astype(np.float64)
        prods.append(N.prod(1) * pan.adm); certs.append((N.min(1) >= 1) * pan.adm); done += pan.P
    pr = np.concatenate(prods); ce = np.concatenate(certs)
    return dict(mean_prod=float(pr.mean()), mean_prod_se=float(pr.std() / np.sqrt(len(pr))),
                cert=float(ce.mean()), cert_se=float(ce.std() / np.sqrt(len(ce))), P=int(len(pr)))

def rebuild_start(k, T, n, start, seed):
    rng = np.random.default_rng(seed); st = State(k, T, n, random.Random(seed))
    if start in ('random', 'complete'):
        for B in ksets(n, k): st.add(int(B))
        if start == 'complete':
            keep = (1 << (k + T)) - 1
            for B in list(st.mem):
                if B & ~keep: st.remove(B)
    elif start.startswith('layer'):
        for B in planted_layer(st, start.split('=', 1)[1]): st.add(int(B))
    else:
        return None
    st.reduce_random(); assert st.covering(); return st

if __name__ == '__main__':
    path = sys.argv[1]; Pbig = int(sys.argv[2]) if len(sys.argv) > 2 else 1000000
    R = json.load(open(path)); k, T, n = R['k'], R['T'], R['n']; c = n - k
    layerF = fwht(np.bincount(ksets(n, k), minlength=1 << n).astype(np.float64))
    out = dict(file=os.path.basename(path), k=k, T=T, n=n, start=R['start'])
    st0 = rebuild_start(k, T, n, R['start'], R['seed'])
    fin = np.load(path.replace('.json', '.npy'))
    st1 = State(k, T, n, random.Random(0))
    for B in fin: st1.add(int(B))
    assert st1.covering(); out['final_covering'] = True
    if st0 is not None:
        assert len(st0.mem) == R['snaps'][0]['size']
        out['start_seven'] = big_stats(st0.members(), n, c, Pbig, 777)
    out['final_seven'] = big_stats(st1.members(), n, c, Pbig, 777)
    # noise reference: random subfamily of the complete layer of the final size
    allk = ksets(n, k); rr = np.random.default_rng(5)
    ref = State(k, T, n, random.Random(0))
    for B in rr.choice(allk, size=len(fin), replace=False): ref.add(int(B))
    m = measures(ref, layerF); out['noise_ref'] = {a: m[a] for a in ('size', 'prop1', 'prop2', 'prop3', 'four_w1', 'four_w2', 'four_w3', 'four_w4')}
    out['noise_ref']['seven'] = big_stats(ref.members(), n, c, Pbig, 777)
    # density exponents (PROGRAMME3_GAMMA conventions): gamma = -ln(|H|/C(n,k))/k ; gamma_a = ln C(k+r,k)/k (finite k)
    # and its limit (1+w) h(w/(1+w)), w = r/k ; eps = (T - 3k/4)/k
    import math
    r = n - T - k; w = r / k; hh = lambda x: 0.0 if x in (0, 1) else -x * math.log(x) - (1 - x) * math.log(1 - x)
    out['gamma_a_finite'] = math.log(math.comb(k + r, k)) / k; out['gamma_a_limit'] = (1 + w) * hh(w / (1 + w))
    out['four_eps'] = 4 * (T - 0.75 * k) / k; out['min_cover_size_bound'] = math.ceil(math.comb(n, k + r) / math.comb(n - k, r))
    g = lambda M: -math.log(M / math.comb(n, k)) / k
    out['gamma_final'] = g(len(fin))
    if st0 is not None: out['gamma_start'] = g(len(st0.mem))
    # dense reference: the complete family; depletion = mean_prod / (p^7 * mean_prod(complete))
    comp = big_stats(allk, n, c, min(Pbig, 200000), 777); out['complete_mean_prod'] = comp['mean_prod']
    p = len(fin) / math.comb(n, k); out['depletion_final'] = out['final_seven']['mean_prod'] / (p ** 7 * comp['mean_prod'])
    if st0 is not None:
        p0 = len(st0.mem) / math.comb(n, k); out['depletion_start'] = out['start_seven']['mean_prod'] / (p0 ** 7 * comp['mean_prod'])
    out['depletion_noise_ref'] = out['noise_ref']['seven']['mean_prod'] / (p ** 7 * comp['mean_prod'])
    print(json.dumps(out), flush=True)
    with open(os.path.join(os.path.dirname(path), 'eval.jsonl'), 'a') as f: f.write(json.dumps(out) + '\n')
