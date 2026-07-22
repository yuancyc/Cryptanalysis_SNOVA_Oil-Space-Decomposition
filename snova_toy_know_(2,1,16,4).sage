# ================================================
# SNOVA Toy — O-known fast verification
# Parameters: v=2, o=1, l=4, q=16
# Assumes known oil subspace O, uses nullspace enumeration
# to rapidly verify the paper's derivation.
# ================================================

import random
from itertools import combinations, product
import time, sys, platform, os, re
from sage.version import version

start_time = time.time()

# ================================================
# 0. Parameters
# ================================================
l = 4; v = 2; o = 1; n = v + o; m = o; q = 16
ambient_dim = n * l   # = 12

print("=" * 65)
print("  SNOVA Toy — v=2, o=1, l=%d, q=16 (O-known)" % l)
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
# 2. Primitive symmetric S (4x4 over F_16)
#    order = q^l - 1 = 16^4 - 1 = 65535 = 3*5*17*257
# ================================================
print("\n[Step 2] Searching primitive symmetric %d x %d S over F_16 ..." % (l, l))
q_order = q^l - 1
divs = [q_order // p for p in [3, 5, 17, 257]]

found = False
attempts = 0
while not found:
    attempts += 1
    diag = [F16.random_element() for _ in range(l)]
    Sc = matrix(F16, l, l)
    for ii in range(l): Sc[ii,ii] = diag[ii]
    for ii in range(l):
        for jj in range(ii+1, l):
            rv = F16.random_element()
            Sc[ii,jj] = rv; Sc[jj,ii] = rv
    poly = Sc.charpoly()
    if not poly.is_irreducible(): continue
    if Sc^q_order != I_l: continue
    if any(Sc^d == I_l for d in divs): continue
    S = Sc; found = True
    if attempts % 100 == 0:
        print("  ... %d attempts" % attempts)
        sys.stdout.flush()

print("  Found after %d attempts: charpoly = %s  (irreducible)" % (attempts, poly))
print("  S =")
for row in S: print("    %s" % list(row))
print("  order(S) = %d = q^l-1  ->  primitive" % q_order)

# F_q[S] = {a0*I + a1*S + a2*S^2 + a3*S^3 | a_i in F_16}
FqS_all = []
for a0 in F16:
    for a1 in F16:
        for a2 in F16:
            for a3 in F16:
                FqS_all.append(a0*I_l + a1*S + a2*S^2 + a3*S^3)
FqS_nonzero = [x for x in FqS_all if not x.is_zero()]
assert len(set(str(x) for x in FqS_all)) == q^l
print("  |F_q[S]| = %d = %d^%d = %d" % (len(FqS_all), q, l, q^l))

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

def same_orbit(Wa,Wb,Sn,maxp=q_order):
    if Wa.rank()<ambient_dim or Wb.rank()<ambient_dim: return (False,None)
    diff=Wa.inverse()*Wb; cur=identity_matrix(F16,ambient_dim)
    for k in range(min(maxp, q_order)):
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
# 11. O-KNOWN FAST ENUMERATION
#    Assumes known oil subspace O = T^{-1}(O_priv).
#    Parametrizes intersection W1O cap (W2O + S^n W2O)
#    via nullspace of [W1O | W2O | S^n W2O].
# ================================================
print("\n" + "=" * 65)
print("  SECTION 11: O-KNOWN NULLSPACE ENUMERATION")
print("=" * 65)

intersection_mat = W1O.augment(W2O).augment(SnW2O)
null_basis = intersection_mat.right_kernel().basis()
nullity = len(null_basis)

print("  Intersection matrix [W1O | W2O | S^n W2O]: %d x %d"
      % (ambient_dim, 3*l*o))
print("  dim(W1O)              = %d  (lo=%d)" % (W1O.rank(), l*o))
print("  dim(W2O+S^n W2O)      = %d  (max 2lo=%d)" % (dim_W2_sum, 2*l*o))
print("  dim(W1O+W2O+S^n W2O)  = %d" % ir)
print("  dim(intersection)     = %d" % dim_inter)
print("  Nullspace dimension   = %d" % nullity)

if dim_inter > 0:
    nc = q^dim_inter
    print("  -> up to 16^%d = %d candidate intersection vectors"
          % (dim_inter, nc))
else:
    print("  -> intersection is {0}, no nontrivial candidates!")

ordered_pairs = [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
solution_y1 = None; solution_y2 = None; solution_y3 = None
found_count = 0

if dim_inter > 0 and nullity > 0:
    total_combos = q^nullity
    print("\n  Nullspace enumeration: 16^%d = %d combos"
          % (nullity, total_combos))

    MAX_ENUM = 5  # 16^5 = 1,048,576

    if nullity <= MAX_ENUM:
        from itertools import product as it_product
        checked = 0
        t0 = time.time()
        print("  Enumerating full nullspace (%d-dim) ..." % nullity)
        sys.stdout.flush()

        for coeffs in it_product(F16, repeat=nullity):
            checked += 1
            if checked % 20000 == 0:
                elapsed = time.time() - t0
                rate = checked / elapsed if elapsed > 0 else 0
                print("    checked %d/%d (%.0f/s) ..."
                      % (checked, total_combos, rate))
                sys.stdout.flush()

            nv = sum(F16(coeffs[j]) * null_basis[j] for j in range(nullity))

            z1 = vector(F16, [nv[c] for c in range(l*o)])
            z2 = vector(F16, [nv[l*o + c] for c in range(l*o)])
            z3 = vector(F16, [nv[2*l*o + c] for c in range(l*o)])

            if z1.is_zero() and z2.is_zero() and z3.is_zero():
                continue

            y1 = O_mat * z1; y2 = O_mat * z2; y3 = O_mat * z3

            ok = True
            for yi in [y1, y2, y3]:
                for M in Mst_list:
                    if yi * M * yi != 0:
                        ok = False; break
                if not ok: break

            if ok:
                for (i, j) in ordered_pairs:
                    yi = [y1, y2, y3][i]; yj = [y1, y2, y3][j]
                    for M in Mst_list:
                        if yi * M * yj != 0:
                            ok = False; break
                    if not ok: break

            if ok:
                found_count += 1
                if solution_y1 is None:
                    solution_y1, solution_y2, solution_y3 = y1, y2, y3
                    print("    Found solution #%d at candidate %d!"
                          % (found_count, checked))
                    break

        elapsed = time.time() - t0
        print("  Enumeration done: %d checked in %.2fs (%.0f/s)"
              % (checked, elapsed, checked/elapsed if elapsed>0 else 0))

    elif dim_inter <= 4:
        from itertools import product as it_product
        checked = 0
        partial_combos = q^dim_inter
        t0 = time.time()
        print("  Nullity=%d too large; partial enumeration over first"
              " %d basis vectors -> 16^%d=%d combos"
              % (nullity, dim_inter, dim_inter, partial_combos))
        sys.stdout.flush()

        for coeffs in it_product(F16, repeat=dim_inter):
            checked += 1
            if checked % 5000 == 0:
                print("    checked %d/%d ..." % (checked, partial_combos))
                sys.stdout.flush()

            nv = sum(F16(coeffs[j]) * null_basis[j]
                    for j in range(dim_inter))

            z1 = vector(F16, [nv[c] for c in range(l*o)])
            z2 = vector(F16, [nv[l*o + c] for c in range(l*o)])
            z3 = vector(F16, [nv[2*l*o + c] for c in range(l*o)])

            if z1.is_zero() and z2.is_zero() and z3.is_zero():
                continue

            y1 = O_mat * z1; y2 = O_mat * z2; y3 = O_mat * z3

            ok = True
            for yi in [y1, y2, y3]:
                for M in Mst_list:
                    if yi * M * yi != 0:
                        ok = False; break
                if not ok: break

            if ok:
                for (i, j) in ordered_pairs:
                    yi = [y1, y2, y3][i]; yj = [y1, y2, y3][j]
                    for M in Mst_list:
                        if yi * M * yj != 0:
                            ok = False; break
                    if not ok: break

            if ok:
                found_count += 1
                if solution_y1 is None:
                    solution_y1, solution_y2, solution_y3 = y1, y2, y3
                    print("    Found at candidate %d!" % checked)
                    break

        elapsed = time.time() - t0
        print("  Partial enum done: %d checked in %.2fs"
              % (checked, elapsed))
    else:
        print("  dim_inter=%d, nullity=%d -- enumeration infeasible."
              % (dim_inter, nullity))
        print("  (This would require a Groebner-basis / XL solver.)")
else:
    if dim_inter <= 0:
        print("\n  dim(intersection)=0 -- no nontrivial y1,y2,y3 exist.")
    if nullity <= 0:
        print("\n  Nullspace is empty.")

# ---------------------------------------------------------------
# 11b. Verify solution & block decomposition
# ---------------------------------------------------------------
print("\n" + "=" * 65)
print("  RESULT & BLOCK DECOMPOSITION")
print("=" * 65)

if solution_y1 is not None:
    print("\n  ATTACK SUCCEEDED")
    print("  Found %d solution(s) via O-known enumeration" % found_count)
    print("  y1 = %s" % list(solution_y1))
    print("  y2 = %s" % list(solution_y2))
    print("  y3 = %s" % list(solution_y3))

    yv = [solution_y1, solution_y2, solution_y3]
    all_ok = True
    for i in range(3):
        for idxM, M in enumerate(Mst_list):
            if yv[i] * M * yv[i] != 0:
                all_ok = False
                print("  FAIL: Q(y%d) fails on M_%d" % (i+1, idxM))
    for (i, j) in ordered_pairs:
        for idxM, M in enumerate(Mst_list):
            if yv[i] * M * yv[j] != 0:
                all_ok = False
                print("  FAIL: B(y%d,y%d) fails on M_%d" % (i+1, j+1, idxM))
    lin_check = (W1_full * solution_y1 + W2_full * solution_y2
                 + Sn_full * W2_full * solution_y3)
    if not lin_check.is_zero():
        all_ok = False
        print("  FAIL: Intersection constraint violated: |lin|=%s"
              % str(list(lin_check))[:80])
    if all_ok:
        print("  All Eq.(4) equations verified (quadratic + bilinear + linear)")

    # Block decomposition
    print("\n  --- Block decomposition (tail of W^{-1} * y_i in O) ---")
    try:
        e = vector(F16, [1] + [0]*(l-1))
        S_powers = {}
        for j in range(q_order):
            S_powers[j] = (S^j) * e

        W1_inv = W1_full.inverse()
        W2_inv = W2_full.inverse()
        SW2_inv = (Sn_full * W2_full).inverse()

        for label, yi, Minv, tag in [
            ("y1", solution_y1, W1_inv,              "W1^{-1}"),
            ("y2", solution_y2, W2_inv,              "W2^{-1}"),
            ("y3", solution_y3, SW2_inv,             "(S^n W2)^{-1}")]:
            w = Minv * yi
            tail = w[l*v : l*n]
            print("  %s * %s in O, tail (last %d) -> o=%d blocks:"
                  % (tag, label, l*o, o))
            for k in range(o):
                block = tail[k*l : (k+1)*l]
                if block.is_zero():
                    print("    block %d: 0  (zero)" % k)
                else:
                    found_j = None
                    for j, se in S_powers.items():
                        if block == se:
                            found_j = j
                            break
                    if found_j is not None:
                        print("    block %d: S^{%d} * e = %s  OK"
                              % (k, found_j, list(block)))
                    else:
                        print("    block %d: %s  FAIL (not in S-orbit of e)"
                              % (k, list(block)))
    except Exception as ex:
        print("  [Block decomposition skipped: %s]" % str(ex)[:100])
else:
    print("\n  No solution found via O-known enumeration.")
    if dim_inter <= 0:
        print("  Reason: intersection is trivial (dim=0).")
        print("  t=3 attack requires dim(W1O cap (W2O + S^n W2O)) > 0.")
        print("  Try re-running for different random W1,W2 in V.")
    elif nullity > 5 and dim_inter > 4:
        print("  Reason: enumeration space too large for exhaustive search.")
        print("  This needs M4GB / XL Groebner-basis solver.")

# ================================================
# FINAL SUMMARY
# ================================================
print("\n" + "=" * 65)
print("  FINAL SUMMARY")
print("=" * 65)
tt = time.time() - start_time
k_val = v // o
print("  SNOVA(v=%d, o=%d, q=%d, l=%d)" % (v, o, q, l))
print("    lv=%d, lo=%d, eqns=%d" % (l*v, l*o, l*l*o))
print("  O-known nullspace enumeration:")
print("    Eqs: %d quad + %d bilin + %d lin = %d total"
      % (3*l*l*o, 6*l*l*o, ambient_dim, 9*l*l*o+ambient_dim))
print("    Vars: %d (y1,y2,y3 in F_q^{ln})" % tot_vars)
w1ok = "OK" if W1_full.rank()==ambient_dim else "FAIL"
w2ok = "OK" if W2_full.rank()==ambient_dim else "FAIL"
orbit_ok = "OK" if not same_orbit(W1_full,W2_full,Sn_full)[0] else "FAIL"
print("    W1: %s  W2: %s  distinct orbits: %s"
      % (w1ok, w2ok, orbit_ok))
print("    dim(intersection) = %d  nullity = %d" % (dim_inter, nullity))
sok = "OK" if solution_y1 is not None else "FAIL"
print("    Solution found: %s  (count: %d)"
      % (sok, found_count))
print("    t=3 %s k=%d" % ("<=" if 3<=k_val else ">", k_val))
print("  Time: %.2f s | Sage: %s" % (tt, version))
print("  Method: O-known + nullspace enumeration (no M4GB/GB)")
print("=" * 65)
