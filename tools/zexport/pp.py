"""Pretty-print declarations from a lean4export ndjson stream (Zellic's proof exports, decompressed, on stdin): the
statement (and with --val, a def's value) of each name in argv (a trailing * matches a prefix). For reading the
lemmas of a published proof as a design reference (PLAN.md G2.0); prints nothing it does not find.
Usage: zstd -dc ID.solution.ndjson.zst | python3 -I tools/zexport/pp.py NAME... [--val]"""
import sys,json
want=set(sys.argv[1:]); prefix=[w[:-1] for w in want if w.endswith('*')]
N={0:''};L={0:'0'};E={}
decls={}
for l in sys.stdin:
    o=json.loads(l)
    if 'in' in o:
        if 'str' in o: p=N[o['str']['pre']]; N[o['in']]=(p+'.' if p else '')+o['str']['str']
        else: p=N[o['num']['pre']]; N[o['in']]=(p+'.' if p else '')+str(o['num']['i'])
    elif 'il' in o:
        if 'succ' in o: L[o['il']]=f"{L[o['succ']]}+1"
        elif 'param' in o: L[o['il']]=N[o['param']]
        elif 'max' in o: L[o['il']]=f"max {L[o['max'][0]]} {L[o['max'][1]]}"
        elif 'imax' in o: L[o['il']]=f"imax {L[o['imax'][0]]} {L[o['imax'][1]]}"
    elif 'ie' in o: E[o['ie']]=o
    else:
        for k in ('thm','def','inductive','axiom','opaque','quot'):
            if k in o:
                d=o[k]
                if isinstance(d,dict) and 'name' in d: decls[N[d['name']]]=(k,d)
                elif k=='inductive':
                    for t in d.get('types',[]): decls[N[t['name']]]=(k,t)
sys.setrecursionlimit(100000)
def pp(i,ctx,depth=0):
    o=E[i]
    if depth>60: return '…'
    if 'bvar' in o:
        j=o['bvar']; return ctx[-1-j] if j<len(ctx) else f"#{j}"
    if 'sort' in o: return f"Sort {L[o['sort']]}"
    if 'const' in o: return N[o['const']['name']].replace('ZellicX86.','')
    if 'app' in o:
        f=[];x=i
        while 'app' in E[x]: f.append(E[x]['app']['arg']); x=E[x]['app']['fn']
        head=pp(x,ctx,depth+1)
        args=[pp(a,ctx,depth+1) for a in reversed(f)]
        return '('+head+' '+' '.join(args)+')'
    if 'lam' in o or 'forallE' in o:
        k='lam' if 'lam' in o else 'forallE'; b=o[k]; n=N[b['name']] or '_'
        n2=n
        while n2 in ctx: n2+="'"
        ty=pp(b['type'],ctx,depth+1); body=pp(b['body'],ctx+[n2],depth+1)
        br={'default':'()','implicit':'{}','instImplicit':'[]','strictImplicit':'⦃⦄'}[b['binderInfo']]
        if k=='lam': return f"(fun {br[0]}{n2} : {ty}{br[1]} => {body})"
        if b['binderInfo']=='instImplicit': return f"[{ty}] → {body}"
        return f"(∀ {br[0]}{n2} : {ty}{br[1]}, {body})"
    if 'letE' in o:
        b=o['letE']; n=N[b['name']]
        return f"(let {n} := {pp(b['value'],ctx,depth+1)}; {pp(b['body'],ctx+[n],depth+1)})"
    if 'proj' in o: return f"{pp(o['proj']['struct'],ctx,depth+1)}.{o['proj']['idx']+1}"
    if 'natVal' in o: return str(o['natVal'])
    if 'strVal' in o: return json.dumps(o['strVal'])
    if 'mdata' in o: return pp(o['mdata']['expr'],ctx,depth)
    return str(o)
for n,(k,d) in decls.items():
    if n in want or any(n.startswith(p) for p in prefix):
        print(f"== {k} {n}\n  : {pp(d['type'],[])}")
        if k=='def' and '--val' in want: print(f"  := {pp(d['value'],[])[:3000]}")
