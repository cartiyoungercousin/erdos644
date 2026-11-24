"""Sanity simulation of Lemma 3 (top-degree request strategy): against greedy and random responders
on ground sets of various sizes, 7 edges always end with max degree <= 4 when 4T >= 3k.
Also checks that T = ceil(3k/4) - 1 can fail (complete family on 7k/4 - 1 points, greedy responder)."""
import random
def play(k, T, n, mode, rng):
    deg = [0] * n
    for step in range(7):
        order = sorted(range(n), key=lambda x: (-deg[x], rng.random()))
        S = set(order[:T]) if step > 0 else set()
        avail = [x for x in range(n) if x not in S]
        if len(avail) < k: return None
        if mode == "greedy":
            avail.sort(key=lambda x: (-deg[x], rng.random()))
            A = avail[:k]
        elif mode == "random":
            A = rng.sample(avail, k)
        else:  # mixed
            avail.sort(key=lambda x: (-deg[x] + rng.random() * 1.5))
            A = avail[:k]
        for x in A: deg[x] += 1
    return max(deg)
rng = random.Random(1)
worst = 0; runs = 0
for k in (4, 8, 12, 16, 20, 23, 30):
    T = -(-3 * k // 4)
    for n in range(k + T, 3 * k + 1):
        for mode in ("greedy", "random", "mixed"):
            for _ in range(20):
                m = play(k, T, n, mode, rng)
                if m is not None:
                    runs += 1; worst = max(worst, m)
print("T=ceil(3k/4): runs", runs, "worst max degree", worst)
k = 8; T = 5; n = 13
print("k=8,T=5 (<3k/4), n=13 greedy:", max(play(k, T, n, "greedy", rng) for _ in range(50)))
