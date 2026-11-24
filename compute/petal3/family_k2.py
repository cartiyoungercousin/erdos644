"""PETAL section 22.1: family test for K2(0.54) at k = 100, T = 75 (c = 54).
Regions R_X (108 points), R_Y (89 points: 1 - 3mu + q with q = 0.175), unlimited fresh points.
Honest family: X-edges with >= 81 points in R_X, Y-edges with >= 71 in R_Y.         tau = (108-80) + (89-70).
Closure family H*: X-edges with >= 55 points in R_X, Y-edges with >= 55 in R_Y.      tau = (108-54) + (89-54).
(tau of a threshold family: an edge avoiding S exists iff some region keeps threshold many points; fresh points are free.)
Six explicit edges of H* with no 2-point cover (exact test)."""
k, T, c = 100, 75, 54
RX = list(range(108)); RY = list(range(108, 197))
print("honest tau =", (108 - 80) + (89 - 70), " closure tau =", (108 - 54) + (89 - 54), " T =", T)
fresh = 10 ** 6
def edge(own):
    global fresh
    E = set(own)
    while len(E) < k: E.add(fresh); fresh += 1
    return E
X = [edge(RX[0:55]), edge(RX[53:108]), edge(RX[0:27] + RX[80:108])]
Y = [edge(RY[0:55]), edge(RY[34:89]), edge(RY[0:28] + RY[62:89])]
six = X + Y
assert all(len(e) == k for e in six)
assert all(len(e & set(RX)) >= 55 for e in X) and all(len(e & set(RY)) >= 55 for e in Y)
types = set()
for x in set().union(*six): types.add(sum(1 << i for i in range(6) if x in six[i]))
print("pairwise overlaps X:", [len(X[i] & X[j]) for i in range(3) for j in range(i + 1, 3)], " Y:", [len(Y[i] & Y[j]) for i in range(3) for j in range(i + 1, 3)])
print("common points X:", len(X[0] & X[1] & X[2]), " Y:", len(Y[0] & Y[1] & Y[2]))
print("2-cover of the six edges exists:", any((a | b) == 63 for a in types for b in types))
