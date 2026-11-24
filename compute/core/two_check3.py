import sys, json, random
import spoil as SP, spoil_two as TW
row = [json.loads(l) for l in open("logs/two_t0.76_N1.9_o0.33_s1_d6.log") if "LEVEL2" in l][0]
E = SP.Engine(0.76, 1.9); nrep = row["nrep"]
m = {int(J): v for J, v in row["pos"].items()}; s = {int(J): v for J, v in row["s"].items()}
d = {7: 0.133, 31: 0.007}
m2 = E.step(m, s, d, 1 << nrep)
for seed in range(int(sys.argv[1]), int(sys.argv[1]) + 2):
    sb, tg = TW.break1(E, m2, nrep + 1, random.Random(seed), 600, 60, starts=5)
    print(seed, "ROBUST" if sb is None else ("broken", SP.fmt(sb)), flush=True)
