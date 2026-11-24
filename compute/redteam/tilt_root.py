import sys, time, json, tilt, tilt_la
T = float(sys.argv[1]); N = float(sys.argv[2]); L = int(sys.argv[3]); tl = float(sys.argv[4]); k = int(sys.argv[5]) if len(sys.argv) > 5 else 0
ref, drop, tag = tilt.load_plans()[k]; t0 = time.time()
z, req = tilt_la.node_solve(T - tilt.MARGIN, N, [], [], tl, drop, ref, L)
print(json.dumps(dict(T=T, N=N, L=L, plan=tag, z=z, secs=round(time.time() - t0), req={str(J): v for J, v in (req or {}).items()})), flush=True)
