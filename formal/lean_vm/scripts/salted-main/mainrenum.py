"""Renumber a span of a deployed `main` module by `mainR` (`BodyK.lean`): python3 mainrenum.py FILE START END."""
import re,sys
def r(k):
    k=int(k)
    if k<26: return k
    if k==26: return 29
    if k==27: return 33
    if k<369: return k+7
    if k<381: return {369:376,370:377,371:378,372:379,379:408,380:409}.get(k,k+7)
    return k+29
def renum(s):
    s=re.sub(r"\.n \((\d+) \+", lambda m: f".n ({r(m.group(1))} +", s)
    s=re.sub(r"\.n (\d+)\b", lambda m: f".n {r(m.group(1))}", s)
    return s
src=open(sys.argv[1]).read()
a=src.index(sys.argv[2]); b=src.index(sys.argv[3])
print(renum(src[a:b]))
