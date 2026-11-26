from cover import min_t, check, requests
cases = {
 'grid L (B\'7,B7 x A\'7,A7), r=4': ({'Bp':7,'B':7,'Ap':7,'A':7}, [('Bp','A'),('B','A'),('B','Ap')], 4),
 'grid L, r=5 (drop E and K? no: F,G + 5)': ({'Bp':7,'B':7,'Ap':7,'A':7}, [('Bp','A'),('B','A'),('B','Ap')], 5),
 'E-frame after K (X6 Y5 A7 B7), r=3': ({'X':6,'Y':5,'A':7,'B':7}, [('X','A'),('Y','B')], 3),
 'grid vs passive (Fd,Gd always avoided), r=4': ({'X':6,'B':7,'A':7,'Y':5}, [('X','A'),('B','A'),('B','Y')], 4),
 'F,G only: 14x14, r=5': ({'F':14,'G':14}, [('F','G')], 5),
}
for name,(S,al,r) in cases.items():
    tt,pl = min_t(S,al,r,tl=100)
    print(name, '-> t =', round(tt,4), 'check', round(check(pl,al,r),4), [ {c:round(v,3) for c,v in q.items()} for q in requests(pl,r)], flush=True)
