"""Renumber a span of a deployed `aggregate_claims` module (`.n k` to `k+2` below 9, `k+22` from 9 on, `AggK.lean`): python3 aggrenum.py FILE START END."""
import re,sys
def r(k):
    k=int(k)
    return k+2 if k<9 else k+22
def renum(s):
    s=re.sub(r"\.n \((\d+) \+", lambda m: f".n ({r(m.group(1))} +", s)
    s=re.sub(r"\.n (\d+)\b", lambda m: f".n {r(m.group(1))}", s)
    return s
src=open(sys.argv[1]).read()
a=src.index(sys.argv[2]); b=src.index(sys.argv[3])
print(renum(src[a:b]))
