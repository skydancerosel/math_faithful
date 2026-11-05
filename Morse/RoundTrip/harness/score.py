import json,glob,os,collections
exp={'same':'equivalent','explicit':'equivalent','restated':'equivalent','stronger':'A_stronger','narrower':'A_narrower','sign':'incomparable'}
rows=[];tab=collections.Counter()
R=os.environ.get('RT_DIR','/tmp/claude-0/rt'); here=os.path.dirname(os.path.abspath(__file__))
for f in sorted(glob.glob(os.path.join(here,'../Items/*.json'))):
    r=json.load(open(f)); i=os.path.basename(f)[:-5]
    k=json.load(open(f'{R}/keys/{i}.json'))['verdict']
    rel=r['relation']; e=exp.get(k)
    m='match' if rel==e else ('partial' if rel=='incomparable' and k in('narrower','stronger') else 'MISMATCH')
    if r.get('not_B') or r.get('A_to_B')=='false': m+=' (B false)'
    tab[(k,rel)]+=1; rows.append((i,k,rel,m,r.get('effort_only')))
for x in rows: print(*x)
print(); [print(k,v) for k,v in sorted(tab.items())]
print(collections.Counter(x[3].split()[0] for x in rows))
