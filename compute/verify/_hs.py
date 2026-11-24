import highspy, numpy as np
inf = highspy.kHighsInf
class MIP:
    def __init__(self):
        self.h = highspy.Highs(); self.h.setOptionValue('output_flag', False); self.n=0
    def var(self, lb, ub, cost=0.0):
        self.h.addVar(lb, ub); self.h.changeColCost(self.n, cost)
        self.h.changeColIntegrality(self.n, highspy.HighsVarType.kInteger); self.n+=1; return self.n-1
    def row(self, idx, lb, ub):
        self.h.addRow(lb, ub, len(idx), np.array(idx,dtype=np.int32), np.ones(len(idx)))
    def rowc(self, idx, coef, lb, ub):
        self.h.addRow(lb, ub, len(idx), np.array(idx,dtype=np.int32), np.array(coef,dtype=float))
    def solve(self):
        self.h.changeObjectiveSense(highspy.ObjSense.kMaximize); self.h.run()
        if self.h.getModelStatus()!=highspy.HighsModelStatus.kOptimal: return None
        return [int(round(v)) for v in self.h.getSolution().col_value]
