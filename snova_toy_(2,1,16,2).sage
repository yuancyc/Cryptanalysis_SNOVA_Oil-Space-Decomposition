# ================================================
# SNOVA Toy — Attack Implementation (M4GB solver)
# Parameters: v=2, o=1, l=2, q=16
# From the attacker's perspective, implementing the
# attack derivation from the paper.
# ================================================

import random
from itertools import combinations, product
import time, sys, platform, os, re
from sage.version import version

start_time = time.time()

# ================================================
# 0. Parameters
# ================================================
l = 2; v = 2; o = 1; n = v + o; m = o; q = 16
ambient_dim = n * l   # = 6

print("=" * 65)
print("  SNOVA Toy — v=2, o=1, l=2, q=16 (M4GB attack)")
print("  lv=%d, lo=%d, eqns=%d, total vars=%d"
      % (l*v, l*o, l*l*o, ambient_dim))
print("=" * 65)

# ================================================
# 1. Field Setup
# ================================================
F16.<alpha> = GF(16)
Rmat = MatrixSpace(F16, l)
I_l = identity_matrix(F16, l)
Z_l = zero_matrix(F16, l)

# ================================================
# Block Matrix Helpers
# ================================================
def block_mat_create(nrows, ncols):
    return [[Z_l for _ in range(ncols)] for _ in range(nrows)]

def block_transpose(M):
    nr, nc = len(M), len(M[0])
    r = block_mat_create(nc, nr)
    for j in range(nr):
        for k in range(nc): r[k][j] = M[j][k]
    return r

def block_mul(A, B):
    ni, nj, nk = len(A), len(A[0]), len(B[0])
    C = block_mat_create(ni, nk)
    for i in range(ni):
        for k in range(nk):
            acc = Z_l
            for j in range(nj): acc += A[i][j]*B[j][k]
            C[i][k] = acc
    return C

def block_quadratic(M, x):
    acc = Z_l
    for j in range(len(x)):
        for k in range(len(x)): acc += x[j].transpose()*M[j][k]*x[k]
    return acc

def block_to_full(blk):
    nr, nc = len(blk), len(blk[0])
    full = zero_matrix(F16, nr*l, nc*l)
    for j in range(nr):
        for k in range(nc):
            for r in range(l):
                for c in range(l): full[l*j+r, l*k+c] = blk[j][k][r,c]
    return full

# ================================================
# 2. Primitive symmetric S
# ================================================
print("\n[Step 2] Primitive symmetric S ...")
divs = [255//p for p in [3,5,17]]
found = False
for s11 in F16:
    if found: break
    for s22 in F16:
        if found: break
        for s12 in F16:
            Sc = matrix(F16,[[s11,s12],[s12,s22]])
            p = Sc.charpoly()
            if not p.is_irreducible(): continue
            if Sc^255!=I_l: continue
            if any(Sc^d==I_l for d in divs): continue
            S = Sc; found = True
assert found
print("  S = [[%s,%s],[%s,%s]] order=255"%(S[0,0],S[0,1],S[1,0],S[1,1]))

FqS_all = [a0*I_l+a1*S for a0 in F16 for a1 in F16]
FqS_nonzero = [x for x in FqS_all if not x.is_zero()]
assert len(FqS_all) == q^l

# ================================================
# 3-5. Keys
# ================================================
print("\n[Step 3-5] Keys ...")
set_random_seed(2025)

F_priv = []
for i in range(m):
    Fi = block_mat_create(n,n)
    for j in range(n):
        for k in range(n):
            if j>=v and k>=v: Fi[j][k]=Z_l
            else: Fi[j][k]=random_matrix(F16,l,l)
    F_priv.append(Fi)

Tblk = block_mat_create(n,n)
for j in range(n): Tblk[j][j] = I_l
for j in range(v):
    for k in range(o): Tblk[j][v+k] = random.choice(FqS_nonzero)

Tt = block_transpose(Tblk)
P_pub = [block_mul(block_mul(Tt,Fi),Tblk) for Fi in F_priv]
print("  Keys generated")

# ================================================
# 6-10. Verification matrices
# ================================================
Sn_full = zero_matrix(F16, ambient_dim, ambient_dim)
for j in range(n): Sn_full[l*j:l*(j+1),l*j:l*(j+1)] = S

Pk_full = [block_to_full(P_pub[k]) for k in range(m)]
T_full = block_to_full(Tblk)
O_mat = T_full[:, l*v:l*n]
assert O_mat.rank() == l*o
for k in range(m):
    for c1 in range(l*o):
        x = O_mat.column(c1)
        assert (x*Pk_full[k])*x == 0
        for c2 in range(c1,l*o):
            y = O_mat.column(c2)
            assert (x*Pk_full[k])*y + (y*Pk_full[k])*x == 0
SnO = Sn_full*O_mat
assert (O_mat.augment(SnO)).rank() == l*o
print("  O verified (lo=%d, S^n-invariant)" % (l*o))

# ================================================
# ATTACK SETUP: Expanded matrices
# ================================================
print("\n" + "=" * 65)
print("  ATTACK SETUP")
print("=" * 65)

expanded = []
for k in range(m):
    for s in range(l):
        for t in range(l):
            M = Sn_full^s * Pk_full[k] * Sn_full^t
            expanded.append((k,s,t,M))
Mst_list = [M for (_,_,_,M) in expanded]
num_exp = len(expanded)
print("  l^2 * m = %d expanded matrices" % num_exp)

def mat_to_vec(M):
    return vector(F16,[M[i,j] for i in range(M.nrows()) for j in range(M.ncols())])

V_gens = [M for (_,_,_,M) in expanded]
V_vecs = [mat_to_vec(M) for M in V_gens]
V_dim = matrix(F16, V_vecs).rank()
V_bv = matrix(F16, V_vecs).row_space().basis()
V_basis = []
for bv in V_bv:
    MM = matrix(F16, ambient_dim, ambient_dim)
    for i in range(ambient_dim):
        for j in range(ambient_dim): MM[i,j] = bv[i*ambient_dim+j]
    V_basis.append(MM)
print("  dim(V) = %d" % V_dim)

def rand_span(basis,sz):
    r = zero_matrix(F16,sz,sz)
    for b in basis:
        c = F16.random_element()
        if c!=0: r+=c*b
    return r

def pick_inv(basis,sz,trials=500):
    for _ in range(trials):
        W=rand_span(basis,sz)
        if W.rank()==sz: return W
    W=rand_span(basis,sz)+identity_matrix(F16,sz)
    return W if W.rank()==sz else identity_matrix(F16,sz)

def same_orbit(Wa,Wb,Sn,maxp=255):
    if Wa.rank()<ambient_dim or Wb.rank()<ambient_dim: return (False,None)
    diff=Wa.inverse()*Wb; cur=identity_matrix(F16,ambient_dim)
    for k in range(min(maxp,q^l)):
        if cur==diff: return (True,k)
        cur=cur*Sn
    return (False,None)

I_full = identity_matrix(F16, ambient_dim)
W1_full = pick_inv(V_basis, ambient_dim)
print("  W1 invertible: %s" % ("OK" if W1_full.rank()==ambient_dim else "FAIL"))

W2_full = None
for _ in range(300):
    Wc=pick_inv(V_basis,ambient_dim)
    if Wc is None: continue
    if not same_orbit(W1_full,Wc,Sn_full)[0]: W2_full=Wc; break
if W2_full is None:
    for _ in range(500):
        Wc=rand_span(V_basis,ambient_dim)+I_full
        if Wc.rank()<ambient_dim: continue
        if not same_orbit(W1_full,Wc,Sn_full)[0]: W2_full=Wc; break
if W2_full is None: W2_full=I_full
print("  W2 invertible: %s, distinct orbit: %s" %
      ("OK" if W2_full.rank()==ambient_dim else "FAIL",
       "OK" if not same_orbit(W1_full,W2_full,Sn_full)[0] else "FAIL"))

W1O=W1_full*O_mat; W2O=W2_full*O_mat; SnW2O=Sn_full*W2O
ir = W1O.augment(W2O).augment(SnW2O).rank()
dim_W2_sum = W2O.augment(SnW2O).rank()
dim_inter = W1O.rank() + dim_W2_sum - ir
print("  dim(W1O cap (W2O + S^n W2O)) = %d" % dim_inter)

tot_vars = 3*ambient_dim
tot_eqns = 9*l*l*o
print("  Eq.(4): %d eqns in %d vars" % (tot_eqns + ambient_dim, tot_vars))

# ================================================
# 11. M4GB ATTACK — direct, no linear elimination
# ================================================
print("\n" + "=" * 65)
print("  SECTION 11: M4GB SOLVER (direct)")
print("  %d equations in %d variables" % (tot_eqns+ambient_dim, tot_vars))
print("=" * 65)

print("\n--- 11a. Polynomial ring ---")
var_names = []
for i in range(3):
    for a in range(ambient_dim):
        var_names.append('y%d_%d'%(i+1,a))
R_poly = PolynomialRing(F16, var_names, order='degrevlex')
y_vars = R_poly.gens()

def y_var(i,a): return y_vars[i*ambient_dim+a]

def gfi(e):
    """Convert GF(16) element -> integer 0..15 via polynomial over GF(2)."""
    bits = e.polynomial().list()
    n = 0
    for i, c in enumerate(bits):
        if c != 0: n |= (1 << i)
    return n

def int_to_f16(n):
    """Convert integer 0..15 -> GF(16) element via polynomial over GF(2)."""
    el = F16(0)
    for i in range(4):
        if (n >> i) & 1:
            el += alpha^i
    return el

print("  F_16[%s,...]  (%d vars)"%(','.join(var_names[:4]),tot_vars))

# --- Build equations ---
print("\n--- 11b. Build equations ---")
eqns = []

for i in range(3):
    for M in Mst_list:
        p = R_poly(0)
        for a in range(ambient_dim):
            for b in range(a,ambient_dim):
                c = M[a,a] if a==b else M[a,b]+M[b,a]
                if c!=0: p += R_poly(c)*y_var(i,a)*y_var(i,b)
        eqns.append(p)

for (i,j) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
    for M in Mst_list:
        p = R_poly(0)
        for a in range(ambient_dim):
            for b in range(ambient_dim):
                c = M[a,b]
                if c!=0: p += R_poly(c)*y_var(i,a)*y_var(j,b)
        eqns.append(p)

SnW2_full = Sn_full*W2_full
for row in range(ambient_dim):
    p = R_poly(0)
    for a in range(ambient_dim):
        c1,c2,c3 = W1_full[row,a],W2_full[row,a],SnW2_full[row,a]
        if c1!=0: p+=R_poly(c1)*y_var(0,a)
        if c2!=0: p+=R_poly(c2)*y_var(1,a)
        if c3!=0: p+=R_poly(c3)*y_var(2,a)
    eqns.append(p)

# Dehomogenize: y1_0 = 1
pin_var = y_var(0,0)
all_eqns = eqns + [pin_var - 1]
print("  %d eqns + y1_0=1 -> %d total" % (len(eqns), len(all_eqns)))

# --- Export to M4GB ---
print("\n--- 11c. Export & M4GB ---")
# Set M4GB_HOME to your local m4gb installation path.
# Ensure the m4gb directory is in the same path as this script.
M4GB_HOME = "/home/yuan/Desktop/m4gb"
# M4GB_HOME = os.path.join(os.getcwd(), "m4gb")
M4GB_INFILE = os.path.join(os.getcwd(), "_snova4_m4gb.in")
M4GB_OUTFILE = M4GB_INFILE.replace('.in','.out')

with open(M4GB_INFILE,'w') as f:
    f.write("$fieldsize %d\n"%q)
    f.write("$vars %s\n"%' '.join(var_names))
    f.write("# %d eqns, %d vars, GF(%d)\n"%(len(all_eqns),tot_vars,q))
    for poly in all_eqns:
        terms=[]
        for coeff,monom in zip(poly.coefficients(),poly.monomials()):
            c=gfi(coeff)
            if c==0: continue
            ms=[]
            for vv in monom.variables():
                e=monom.degree(vv)
                ms.append(str(vv) if e==1 else "%s^%d"%(str(vv),e))
            if not ms: terms.append(str(c))
            elif c==1: terms.append("*".join(ms))
            else: terms.append("%d*%s"%(c,"*".join(ms)))
        f.write((" + ".join(terms) if terms else "0")+'\n')
print("  Exported: %d vars, %d eqns"%(tot_vars,len(all_eqns)))

# --- Run M4GB ---
t_start = time.time()
all_solutions = []
m4gb_used = False

if os.path.isdir(M4GB_HOME) and os.path.isfile(os.path.join(M4GB_HOME,"solver.sh")):
    print("  Running M4GB ...")
    sys.stdout.flush()
    import subprocess
    try:
        r = subprocess.run(
            ["bash",os.path.join(M4GB_HOME,"solver.sh"),
             "-f",str(q),"-n",str(tot_vars),"-v","1",
             M4GB_INFILE,M4GB_OUTFILE],
            cwd=M4GB_HOME, capture_output=True, text=True, timeout=3600)
        if r.returncode==0:
            print("  M4GB done (rc=0)")
        else:
            print("  M4GB rc=%d"%r.returncode)
            t=(r.stderr or "")[-500:]
            if t: print("  stderr: %s"%t)
    except FileNotFoundError:
        print("  WARNING: bash not available")
    except Exception as e:
        print("  M4GB error: %s"%str(e)[:200])
else:
    print("  M4GB not found at %s, skipping." % M4GB_HOME)
    print("  Please set M4GB_HOME to your m4gb installation directory.")

# --- Parse M4GB output ---
if os.path.isfile(M4GB_OUTFILE):
    out_lines = []
    with open(M4GB_OUTFILE,'r') as f:
        out_lines = [L.strip() for L in f if L.strip() and not L.startswith('#')]
    print("  M4GB output: %d GB polynomials" % len(out_lines))
    for L in out_lines[:5]:
        print("    %s" % L)
    if len(out_lines) > 5:
        print("    ... (%d more)" % (len(out_lines)-5))

    gb_polys = []
    for line in out_lines:
        p = R_poly(0)
        for term_str in [t.strip() for t in line.split('+') if t.strip()]:
            m = re.match(r'^(\d+)\*(.+)', term_str)
            if m:
                coeff_int = int(m.group(1))
                mono_str = m.group(2)
            elif term_str.isdigit():
                coeff_int = int(term_str)
                mono_str = '1'
            else:
                coeff_int = 1
                mono_str = term_str
            coeff = int_to_f16(coeff_int % 16)
            if coeff != 0:
                p += coeff * R_poly(mono_str)
        if p != 0:
            gb_polys.append(p)

    print("  Parsed %d nonzero GB polynomials" % len(gb_polys))
    if len(gb_polys) > 0:
        try:
            I_gb = R_poly.ideal(gb_polys)
            dim_gb = I_gb.dimension()
            print("  dim(GB ideal) = %d" % dim_gb)
            if dim_gb == 0:
                sols = I_gb.variety()
                print("  M4GB -> Sage: %d solutions!" % len(sols))
                all_solutions = sols
                m4gb_used = True
            elif dim_gb == 1:
                print("  dim=1 -- scanning y1_1 over F_16 ...")
                v2 = y_var(0, 1)
                for t in F16:
                    try:
                        I_t = R_poly.ideal(gb_polys + [v2 - t])
                        if I_t.dimension() == 0:
                            for s in I_t.variety():
                                all_solutions.append(s)
                    except Exception: continue
                print("  M4GB+Sage: %d solutions!" % len(all_solutions))
                if len(all_solutions) > 0: m4gb_used = True
            else:
                print("  dim=%d -- scanning F_16^2 ..." % dim_gb)
                v2, v3 = y_var(0, 1), y_var(0, 2)
                for t2 in F16:
                    for t3 in F16:
                        try:
                            I_tt = R_poly.ideal(gb_polys + [v2 - t2, v3 - t3])
                            if I_tt.dimension() == 0:
                                for s in I_tt.variety():
                                    all_solutions.append(s)
                        except Exception: continue
                print("  Scanned: %d solutions" % len(all_solutions))
                if len(all_solutions) > 0: m4gb_used = True
        except Exception as e:
            print("  Sage variety() on M4GB GB failed: %s" % str(e)[:200])

# --- Fallback: Sage slimgb ---
if not m4gb_used:
    print("\n  Falling back to Sage slimgb on full system ...")
    sys.stdout.flush()
    try:
        I_full = R_poly.ideal(all_eqns)
        G_full = I_full.groebner_basis('singular:slimgb')
        dim_full = I_full.dimension()
        print("  dim=%d, |GB|=%d"%(dim_full,len(G_full)))
        if dim_full==0:
            sols=I_full.variety()
            print("  %d solutions!"%len(sols))
            all_solutions=sols
        elif dim_full==1:
            v2=y_vars[1]
            for tv in F16:
                try:
                    for s in R_poly.ideal(all_eqns+[v2-tv]).variety():
                        all_solutions.append(s)
                except Exception: continue
            print("  Scanned: %d solutions"%len(all_solutions))
        else:
            v2,v3=y_vars[1],y_vars[2]
            for t2 in F16:
                for t3 in F16:
                    try:
                        for s in R_poly.ideal(all_eqns+[v2-t2,v3-t3]).variety():
                            all_solutions.append(s)
                    except Exception: continue
            print("  Scanned: %d solutions"%len(all_solutions))
    except Exception as e:
        print("  Sage GB failed: %s"%str(e)[:200])

# ---------------------------------------------------------------
# 11d. Verify
# ---------------------------------------------------------------
print("\n--- 11d. Verify ---")

found_sol = None
if len(all_solutions)==0:
    print("  No solutions. t=3 > k=%d for v=%d,o=%d."%(v//o,v,o))
else:
    print("  %d solutions" % len(all_solutions))
    for idx, sol in enumerate(all_solutions):
        y0 = vector(F16,[sol[y_var(0,a)] for a in range(ambient_dim)])
        y1 = vector(F16,[sol[y_var(1,a)] for a in range(ambient_dim)])
        y2 = vector(F16,[sol[y_var(2,a)] for a in range(ambient_dim)])
        yv = [y0,y1,y2]
        ok=True
        for i in range(3):
            for M in Mst_list:
                if yv[i]*M*yv[i]!=0: ok=False
        for (i,j) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
            for M in Mst_list:
                if yv[i]*M*yv[j]!=0: ok=False
        if not (W1_full*y0+W2_full*y1+SnW2_full*y2).is_zero(): ok=False
        if ok and found_sol is None: found_sol=(y0,y1,y2)
        if idx<3: print("  Sol %d: %s"%(idx+1,"OK" if ok else "FAIL"))

# ---------------------------------------------------------------
# 11e. Result
# ---------------------------------------------------------------
print("\n" + "=" * 65)
if found_sol is not None:
    y1_s,y2_s,y3_s=found_sol
    print("  ATTACK SUCCEEDED")
    print("  y1 = %s" % list(y1_s))
    print("  y2 = %s" % list(y2_s))
    print("  y3 = %s" % list(y3_s))

    e = vector(F16,[1]+[0]*(l-1))
    Sp = {j:(S^j)*e for j in range(255)}
    for label,yi,Minv,tag in [
        ("y1",y1_s,W1_full.inverse(),"W1^{-1}"),
        ("y2",y2_s,W2_full.inverse(),"W2^{-1}"),
        ("y3",y3_s,(Sn_full*W2_full).inverse(),"(S^n W2)^{-1}")]:
        w=Minv*yi; tail=w[int(l*v):int(l*n)]
        print("    %s * %s -> tail=%s"%(tag,label,list(tail)))
        for k in range(o):
            blk=tail[int(k*l):int((k+1)*l)]
            if blk.is_zero():
                print("      block %d: 0"%k)
            else:
                fj=None
                for j,se in Sp.items():
                    if blk==se: fj=j; break
                if fj is not None: print("      block %d: S^{%d} * e  OK"%(k,fj))
                else: print("      block %d: %s  FAIL"%(k,list(blk)))
else:
    print("  No solution. t=3 > k=%d. Try t=2."%(v//o))

# ================================================
# Summary
# ================================================
print("\n" + "=" * 65)
print("  FINAL SUMMARY")
print("=" * 65)

kv = v//o
print("""  SNOVA(v={v}, o={o}, q={q}, l={l})
    lv={lv}, lo={lo}, eqns={eqns}

  M4GB attack (no O, direct):
    Eqs: {nq} quad + {nb} bilin + {nl} lin + 1 dehomog = {ntot}
    Vars: {nvars}
    W1: {w1}  W2: {w2}  dim(intersect)={dim_inter}
    Solutions: {nsol} {solved}
    t=3 {t3op} k={kv} -> {t3note}

  Time: {tt:.2f}s | Sage: {ver}
""".format(
    v=v,o=o,q=q,l=l,lv=l*v,lo=l*o,eqns=l*l*o,
    nq=3*l*l*o,nb=6*l*l*o,nl=ambient_dim,ntot=9*l*l*o+ambient_dim+1,
    nvars=tot_vars,
    w1="OK" if W1_full.rank()==ambient_dim else "FAIL",
    w2="OK" if W2_full.rank()==ambient_dim else "FAIL",
    dim_inter=dim_inter,
    nsol=len(all_solutions),
    solved="OK" if len(all_solutions)>0 else "FAIL",
    kv=kv,t3op="<=" if 3<=kv else ">",
    t3note=("works!" if len(all_solutions)>0 else "generically trivial, use t=2"),
    tt=time.time()-start_time, ver=version))
print("=" * 65)