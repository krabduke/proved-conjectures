# Numerically check the three Coman Carmichael conjectures (A182132, A182088, A182207).
def isprime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d//=2; s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def korselt(fs):
    C = 1
    for f in fs: C *= f
    return len(set(fs)) == len(fs) and all((C-1) % (p-1) == 0 for p in fs)
cnt=[0,0]; bad=[0,0]
for n in range(1,300000):
    a=[30*n-7,90*n-23,300*n-79]
    if all(map(isprime,a)): cnt[0]+=1; bad[0]+= not korselt(a)
    b=[30*n-29,60*n-59,90*n-89,180*n-179]
    if all(map(isprime,b)): cnt[1]+=1; bad[1]+= not korselt(b)
print("A182132: prime cases", cnt[0], "failures", bad[0])
print("A182088: prime cases", cnt[1], "failures", bad[1])
# A182207: for Carmichael numbers C (brute force, small) and every prime p with p, 2p-1 | C,
# check C/(p(2p-1)) == p mod (2p-2).
def factor(n):
    f=[]; d=2
    while d*d<=n:
        while n%d==0: f.append(d); n//=d
        d+=1
    if n>1: f.append(n)
    return f
car=0; bad3=0; cases=0
for C in range(3, 3_000_000, 2):
    fs=factor(C)
    if len(fs)<2 or not korselt(fs): continue
    car+=1
    for p in fs:
        if p>2 and C % (2*p-1)==0 and isprime(2*p-1):
            cases+=1
            m=C//(p*(2*p-1))
            bad3 += (m-p) % (2*p-2) != 0
print("A182207: Carmichael numbers <3e6:", car, "cases", cases, "failures", bad3)
