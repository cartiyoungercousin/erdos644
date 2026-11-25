"""Independent verifier for a produced seven (written fresh; imports nothing from b1/task3).
Checks: 7 pairwise distinct sets; each has size k and syndrome alpha under the ORIGINAL parity-check rows;
no transversal of size <= 2, by brute force over all point pairs {x, y} (x = y allowed) of V."""


def popc(x):
    return bin(x).count('1')


def verify(n, Hrows, alpha, k, B):
    if len(B) != 7:
        return False, 'not seven'
    if len(set(B)) != 7:
        return False, 'not distinct'
    for S in B:
        if popc(S) != k:
            return False, 'size'
        syn = sum(((popc(S & h) & 1) << i) for i, h in enumerate(Hrows))
        if syn != alpha:
            return False, 'not a member'
    for x in range(n):
        for y in range(x, n):
            m = (1 << x) | (1 << y)
            if all(S & m for S in B):
                return False, 'transversal %d %d' % (x, y)
    return True, 'ok'
