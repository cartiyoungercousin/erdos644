r"""Second-solver check of the extremal (seven-free) families: criterion tau, CP-SAT (127 co-types) and HiGHS MILP
(monotone form) must both say 'no good seven'; for small n also explicit enumeration (brute.py, Glucose).
usage: verify_extremal.py idx   (one family per call, for parallel runs)"""
import json, sys, time
import cells, seven_milp, brute
FAMS = [  # (k, a, J first coordinates or None = complete)
    (8, (13,), None), (9, (16,), None), (10, (17,), None), (11, (19,), None), (13, (23,), None), (14, (24,), None),
    (15, (26,), None), (17, (30,), None), (18, (31,), None), (19, (33,), None),
    (12, (11, 11), 'odd'), (12, (10, 12), 'odd'), (16, (14, 15), 'odd'), (16, (13, 16), 'odd'), (20, (18, 18), 'odd'),
    (20, (16, 20), 'odd'), (20, (17, 19), 'odd')]
if __name__ == '__main__':
    k, a, kind = FAMS[int(sys.argv[1])]
    U = cells.universe(a, k)
    J = U if kind is None else [j for j in U if j[0] % 2 == 1]
    t0 = time.time()
    tau = cells.tau_of(a, k, J)
    st1 = cells.find_seven(a, k, J, 7200)[0]
    st2 = seven_milp.seven_milp(a, k, J, 7200)
    out = dict(k=k, a=a, J=kind or 'complete', n=sum(a), tau=tau, cpsat=st1, milp=st2)
    if sum(a) <= 0:  # explicit SAT on complete families is a hard symmetric UNSAT; skipped
        M = brute.members(a, k, J)
        out['explicit_tau'] = brute.tau_brute(sum(a), M) if sum(a) <= 13 else None
        out['explicit_seven'] = brute.seven_brute(sum(a), M)
    out['secs'] = round(time.time() - t0)
    print(json.dumps(out), flush=True)
