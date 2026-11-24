"""Tiny LP/MILP builder on highspy (pulp 4.x changed its API).  Expressions are dicts {var: coef} plus constant."""
import highspy
INF = highspy.kHighsInf


class LP:
    def __init__(self):
        self.h = highspy.Highs(); self.h.setOptionValue("output_flag", False); self.n = 0; self.ints = []

    def var(self, lo=0.0, hi=INF, cost=0.0, integer=False):
        self.h.addCol(cost, lo, hi, 0, [], [])
        if integer: self.h.changeColIntegrality(self.n, highspy.HighsVarType.kInteger)
        self.n += 1; return self.n - 1

    def row(self, terms, lo, hi):
        """terms: list of (var, coef); lo <= sum <= hi"""
        acc = {}
        for v, cf in terms: acc[v] = acc.get(v, 0.0) + cf
        idx = [v for v in acc if acc[v] != 0.0]
        self.h.addRow(lo, hi, len(idx), idx, [acc[v] for v in idx])

    def solve(self, maximize=False):
        if maximize: self.h.changeObjectiveSense(highspy.ObjSense.kMaximize)
        self.h.run()
        st = self.h.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal: return None, None
        return self.h.getInfo().objective_function_value, list(self.h.getSolution().col_value)
