"""TWIN 18.6 F3: on the saved class-(T) line at N = 1.9k check |M_6| + |W| + |G_4| against 2t and Phi against 2(N+t) - 5.
Kept replies 1,2,3,4,6 are relabelled 1..5 (state after the original reply 6, before request 7)."""
import json, fano_read as f
d = [json.loads(l) for l in open("nb_0.log") if l.startswith("{")][0]
m, real, hist = f.simulate(d); st = hist[5][0]; N = d["Ns"][0]
kept = [0, 1, 2, 3, 5]
def proj(J): return sum(1 << n for n, i in enumerate(kept) if (J >> i) & 1)
mass = {}
for J, v in st.items(): mass[proj(J)] = mass.get(proj(J), 0.0) + v
has = lambda J, *idx: all((J >> (i - 1)) & 1 for i in idx)
M6 = sum(v for J, v in mass.items() if has(J, 1, 3) or has(J, 2, 5))
W = sum(v for J, v in mass.items() if has(J, 1, 2) or has(J, 3, 5))
G4 = sum(v for J, v in mass.items() if has(J, 4) and not (has(J, 1, 3) or has(J, 2, 5) or has(J, 1, 2) or has(J, 3, 5)))
pc = lambda J: bin(J).count("1")
Phi = (M6 + W + G4) - 5 + 2 * N
tot = sum(pc(J) * v for J, v in mass.items())
print(f"N={N} budget t={d['T']}: |M_6|={M6:.4f} |W|={W:.4f} |G_4|={G4:.4f} sum={M6+W+G4:.4f}  vs 2t={2*d['T']:.4f}")
print(f"  incidences {tot:.4f} (=5), total mass {sum(mass.values()):.4f} (=N);  Phi = sum - 5 + 2N = {Phi:.4f}  vs allowance 2(N+t)-5 = {2*(N+d['T'])-5:.4f}")
print(f"  (E): |M_6|<=t {M6 <= d['T']+1e-9}, |W|<=t {W <= d['T']+1e-9}, sum<=2t {M6+W+G4 <= 2*d['T']+1e-9}")
