import sys, random
import jprime_j2_verify as V
rng = random.Random(int(sys.argv[1]))
games = int(sys.argv[2])
cases = [
 ("c.4 Jpp bdry",600,450,240,22,'Jpp'), ("c.4 Jp bdry",600,450,240,15,'Jp'),
 ("c.62 Jpp bdry",600,450,372,55,'Jpp'), ("c.62 Jp bdry",600,450,372,37,'Jp'),
 ("t.7 c.55 Jpp",600,420,330,37,'Jpp'), ("t.7 c.55 Jp",600,420,330,25,'Jp'),
 ("t.9 c.55 Jpp",600,540,330,52+15,'Jpp'), ("t.9 c.4 Jp",600,540,240,45,'Jp'),
 # over boundary (hypothesis violated) -- non-vacuity: expect budget failures
 ("OVER Jpp c.5 MU+4",600,450,300,41,'Jpp'), ("OVER Jp c.5 MU+4",600,450,300,29,'Jp'),
]
for lab,k,T,C,MU,thm in cases:
    over = lab.startswith("OVER")
    st = dict(g=0,win=0,budget=0,cover=0,maxc3=0)
    for g in range(games):
        V.Ctr.n=0
        petals = V.random_config(k,C,rng) if g%2 else None
        if petals is None:
            s1 = V.step1(k,T,C,MU,rng,rng.choice(['AAAAAAA','AABABAB','AAAABBB','ABBBAAA']),rng.choice(['keepI','fresh','overlap','random']))
            if s1 is None: continue
            petals = s1[0]
        for filler in ('random','single','multi'):
            for om in ('adv','maxU','random'):
                r = V.step2(petals,k,T,C,MU,thm,rng,om,filler,adaptive_a=bool(g%3==0),fixed_a=rng.randrange(4))
                st['g']+=1
                if not r['ok']: st['budget']+=1; continue
                st['win']+=1; st['maxc3']=max(st['maxc3'],r['costs'][2])
                if r['cover']: st['cover']+=1
    hyp = (k-C)+(4 if thm=='Jpp' else 6)*MU
    print(lab, "T",T,"hyp-bound",hyp, st, flush=True)
