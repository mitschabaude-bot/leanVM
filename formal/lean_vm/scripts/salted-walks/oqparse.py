"""The numbers of the salted `opening_queries` walk instances: the deployed instances' shapes
(`WalkOqOk*.lean`) by name, the statements' indices and values from the scan of the salted bodies.
Writes `WORK/oqinst.json` for `oqgen.py`.

Run from lean_vm/: python3 -I scripts/salted-walks/oqparse.py WORK, WORK the directory holding
`compare.tsv` (`lake env lean --run scripts/salted-walks/Compare.lean WORK`) and `oqscan.txt`
(`lake env lean --run scripts/salted-walks/OqScan.lean NAMES… > WORK/oqscan.txt`). The modules it
writes are checked by the kernel; they are not trusted.
"""
import sys
from pathlib import Path
LEAN_VM = Path(__file__).resolve().parent.parent.parent
WORK = Path(sys.argv[1])
import re, json
G=str(LEAN_VM / 'LeanVM/Guest') + '/'
cmpD={}
for l in open(WORK / 'compare.tsv'):
    p=l.rstrip('\n').split('\t')
    if p[1]!='-': cmpD[int(p[1])+1]=(int(p[0])+1,p[3])
ok=''.join(open(G+f'WalkOqOk{k}.lean').read() for k in range(4))
inst=[]
for m in re.finditer(r"theorem walkOk_(\d+) : (mainOkS|loop1Ok|loop0Ok) (\d+) (?:(\d+) )?⟨(\d+), (\d+), (\d+), (\d+)⟩ = true", ok):
    jd,kind,_,odd,base,I,pd,cd=m.groups()
    js,name=cmpD[int(jd)]
    inst.append(dict(jd=int(jd),js=js,name=name,kind=kind,odd=int(odd) if odd else 0,base=int(base),I=int(I),pd=int(pd),cd=int(cd)))
scan={}
for l in open(WORK / 'oqscan.txt'):
    p=l.rstrip('\n').split('\t')
    j=int(p[0]); ci=int(p[2].split('=')[1])
    atoms={}
    for a in p[4].strip('[]').split(', '):
        i,t=a.split(':',1); atoms[int(i)]=t
    scan[j]=(p[1],ci,atoms)
out=[]
for d in inst:
    nm,ci,at=scan[d['js']]
    assert nm==d['name'],(nm,d)
    if d['kind']=='mainOkS':
        src=[]
        if d['odd']==1:
            i=[k for k,t in at.items() if re.fullmatch(r'load \d+ 4 0',t)][0]
            w=int(at[i].split()[1]); d['load']=(i,w); src=[(w,i+1)]
        d['src']=src
    else:
        c=at[ci-2]; x=at[ci-1]
        assert c.startswith('const') and x.startswith('mul') and x.split()[2]=='0' and x.split()[3]==c.split()[1], (c,x)
        d['tail']=(ci,int(c.split()[1]),int(x.split()[1]))
        a0=at[0].split(); assert a0[0]=='mul' and a0[2]=='2' and a0[3]=='0'
        if d['kind']=='loop1Ok':
            a1=at[1].split(); a2=at[2].split()
            assert a1[0]=='mul' and a1[2]==a0[1] and a1[3]=='0' and a2[0]=='load' and a2[2]==a1[1] and a2[3]==str(d['odd'])
            k2=[k for k,t in at.items() if t.startswith('load') and t.split()[2]==a1[1] and t.split()[3]==str(d['odd']+1)]
            assert len(k2)==1
            k2=k2[0]; w2=int(at[k2].split()[1])
            d['atoms']=(int(a0[1]),int(a1[1]),int(a2[1]),k2,w2)
            d['src']=[(int(a2[1]),3),(w2,k2+1)]
        else:
            a1=at[1].split(); assert a1[0]=='load' and a1[2]==a0[1] and a1[3]=='0'
            d['atoms']=(int(a0[1]),int(a1[1]))
            d['src']=[(int(a1[1]),2)]
    out.append(d)
json.dump(out,open(WORK / 'oqinst.json','w'))
print(len(out)); print(out[0]); print(out[1]); print([d for d in out if d['kind']=='loop0Ok'][0])
