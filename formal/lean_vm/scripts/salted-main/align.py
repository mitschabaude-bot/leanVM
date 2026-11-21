"""Align a deployed and a salted core function statement by statement, numbers abstracted.

  python3 align.py DEPLOYED_DATA_DIR K SALTED_DATA_DIR K' MAP_OUT.json [i0 i1 j0 j1]

Prints the changed statements (stderr) and writes the map from the deployed function's values to
the salted one's, read off the equal statements (`mainR` in `SaltedGuest/B1/Main/BodyK.lean`).
"""
import re,sys,difflib,json,glob
def body(datadir, k):
    files=sorted(glob.glob(datadir+'/Core*.lean'))
    txt=''
    for f in files:
        s=open(f).read()
        m=re.search(r'^namespace core%d\n(.*?)^end core%d\n'%(k,k), s, re.M|re.S)
        if m: txt=m.group(1); break
    # collect chunk defs in order of 'body := ' composition; simpler: take all stmt lines in file order of defs c0..
    defs=re.findall(r'noncomputable def (\w+) : List Core.Stmt := (.*?)(?=\n/--|\Z)', txt, re.S)
    d=dict(defs)
    b=d['body']
    order=re.findall(r'\b(c\d+|b\d+)\b', b) if '++' in b else ['body']
    stm=[]
    for name in order:
        t=d[name]
        for line in t.split('\n'):
            line=line.strip()
            if line.startswith('.'): stm.append(line.rstrip(' ::').rstrip(','))
    return stm
dep=body(sys.argv[1], int(sys.argv[2])); sal=body(sys.argv[3], int(sys.argv[4]))
norm=lambda s: re.sub(r'\.n \d+','.n #',s)
sm=difflib.SequenceMatcher(None,[norm(x) for x in dep],[norm(x) for x in sal],autojunk=False)
mp={}
conf=set()
for tag,i1,i2,j1,j2 in sm.get_opcodes():
    if tag=='equal':
        for a,b in zip(dep[i1:i2],sal[j1:j2]):
            for x,y in zip(re.findall(r'\.n (\d+)',a),re.findall(r'\.n (\d+)',b)):
                x=int(x);y=int(y)
                if x in mp and mp[x]!=y: conf.add(x)
                mp.setdefault(x,y)
    else:
        print(tag, f"dep[{i1}:{i2}]", f"sal[{j1}:{j2}]", file=sys.stderr)
        for a in dep[i1:i2]: print('  -',a[:150],file=sys.stderr)
        for b in sal[j1:j2]: print('  +',b[:150],file=sys.stderr)
print(len(dep),len(sal),'conflicts',sorted(conf),file=sys.stderr)
json.dump(mp,open(sys.argv[5],'w'))
if len(sys.argv)>6:
    a,b,c,d=map(int,sys.argv[6:10])
    print('DEP'); [print(i,x[:200]) for i,x in enumerate(dep) if a<=i<b]
    print('SAL'); [print(i,x[:200]) for i,x in enumerate(sal) if c<=i<d]
