import os, re, json
# Requires a local clone of the official OEIS data:
#   git clone --depth 1 https://github.com/oeis/oeisdata.git data/oeisdata
root = "data/oeisdata/seq"
out = []
for d in sorted(os.listdir(root)):
    p = os.path.join(root, d)
    if not os.path.isdir(p): continue
    for f in os.listdir(p):
        if not f.endswith(".seq"): continue
        txt = open(os.path.join(p, f), encoding="utf-8", errors="replace").read()
        if "onjecture" not in txt: continue
        lines = txt.splitlines()
        A = f[:-4]
        name = next((l[11:] for l in lines if l.startswith("%N")), "")
        kw = next((l[11:] for l in lines if l.startswith("%K")), "")
        conj = [l[11:] for l in lines if l[:2] in ("%C","%F","%e") and re.search(r"[Cc]onjecture", l)]
        progs = "".join(l[1] for l in lines if l[:2] in ("%o","%p","%t"))
        out.append(dict(A=A, name=name, kw=kw, conj=conj, has_prog=bool(progs), n_lines=len(lines)))
json.dump(out, open("data/conjectures.json","w"))
print(len(out), "entries with conjectures")
print(sum(1 for o in out if "dead" not in o["kw"]), "not dead")
