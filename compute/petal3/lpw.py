"""Minimal linear-expression wrapper over highspy (pulp 4.x API differs; design.py also uses highspy directly)."""
import highspy
INF = highspy.kHighsInf
class E:
    __slots__ = ("d", "c")
    def __init__(s, d=None, c=0.0): s.d = d or {}; s.c = c
    def __add__(s, o):
        o = toE(o); d = dict(s.d)
        for k, v in o.d.items(): d[k] = d.get(k, 0.0) + v
        return E(d, s.c + o.c)
    __radd__ = __add__
    def __neg__(s): return E({k: -v for k, v in s.d.items()}, -s.c)
    def __sub__(s, o): return s + (-toE(o))
    def __rsub__(s, o): return toE(o) + (-s)
    def __mul__(s, f): return E({k: v * f for k, v in s.d.items()}, s.c * f)
    __rmul__ = __mul__
def toE(o): return o if isinstance(o, E) else E({}, float(o))
def esum(xs):
    d = {}; c = 0.0
    for x in xs:
        x = toE(x); c += x.c
        for k, v in x.d.items(): d[k] = d.get(k, 0.0) + v
    return E(d, c)
class Model:
    def __init__(s, msg=False, tl=600):
        s.h = highspy.Highs(); s.h.setOptionValue("output_flag", msg); s.h.setOptionValue("time_limit", float(tl)); s.n = 0
    def var(s, lo=0.0, hi=INF, integer=False):
        s.h.addVar(lo, hi)
        if integer: s.h.changeColIntegrality(s.n, highspy.HighsVarType.kInteger)
        s.n += 1; return E({s.n - 1: 1.0})
    def _row(s, e, lo, hi):
        idx = list(e.d); s.h.addRow(lo - e.c if lo > -INF else -INF, hi - e.c if hi < INF else INF, len(idx), idx, [e.d[i] for i in idx])
    def le(s, a, b): s._row(toE(a) - toE(b), -INF, 0.0)
    def eq(s, a, b): s._row(toE(a) - toE(b), 0.0, 0.0)
    def minimize(s, e):
        for i, v in e.d.items(): s.h.changeColCost(i, v)
        s.h.run()
        s.sol = s.h.getSolution().col_value
        return s.h.modelStatusToString(s.h.getModelStatus()), s.h.getInfo().objective_function_value + e.c
    def val(s, e): e = toE(e); return e.c + sum(v * s.sol[i] for i, v in e.d.items())
