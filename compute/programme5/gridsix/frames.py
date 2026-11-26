"""Frames (sevens that may drop E, F, G or K) after the critical triple and Theorem P's K.  Units k/14.
Base cells after K (alpha = |A|): X=6 (E,F), Y=5 (E,G), A (G,K), B (F,K), Ep=3 (E), Fd (F), Gd (G), Z = F&G (0+,
avoided by K), plus outside points.  An answer M_j is given by its mass on each atom (refined cell) and on outside
points; outside points are never in an alive pair of any frame considered here (proved by hand: every frame keeps
three of E, F, G, K and E&F&K = E&G&K = E&F&G = F&G&K - Z = 0), so only atom masses matter for alive pairs.
alive(frame) lists the alive atom pairs: (p, q), p = q allowed, such that every member of the frame contains p or q.
"""
import itertools

ZEPS = 1e-3
BASE = ['X', 'Y', 'A', 'B', 'Ep', 'Fd', 'Gd', 'Z']
MEMB = {'E': {'X', 'Y', 'Ep'}, 'F': {'X', 'B', 'Fd', 'Z'}, 'G': {'Y', 'A', 'Gd', 'Z'}, 'K': {'A', 'B'}}


def base_sizes(al=7.0):
    return {'X': 6.0, 'Y': 5.0, 'A': al, 'B': 14.0 - al, 'Ep': 3.0, 'Fd': al - 6.0, 'Gd': 9.0 - al, 'Z': ZEPS}


def refine(sizes, answers):
    """answers: list of dicts atom-key -> mass inside the answer, where atom keys are tuples (cell, b1, ..., bj-1)
    for the j-th answer.  Returns {atom: mass} with atom = (cell, b1, ..., bm)."""
    atoms = {(c,): s for c, s in sizes.items()}
    for M in answers:
        new = {}
        for a, s in atoms.items():
            inside = min(s, max(0.0, M.get(a, 0.0)))
            new[a + (1,)] = inside; new[a + (0,)] = s - inside
        atoms = new
    return atoms


def member_has(name, atom):
    """is atom in member name (E, F, G, K, or 'M1', 'M2', ...)"""
    if name[0] == 'M': return atom[int(name[1:])] == 1
    return atom[0] in MEMB[name]


def alive(atoms, frame, tiny=1e-9):
    live = [a for a, s in atoms.items() if s > tiny]
    out = []
    for i, p in enumerate(live):
        for q in live[i:]:
            if all(member_has(m, p) or member_has(m, q) for m in frame): out.append((p, q))
    return out


def endpoints(atoms, frame):
    al = alive(atoms, frame)
    U = set(x for pq in al for x in pq)
    return sum(atoms[a] for a in U), U
