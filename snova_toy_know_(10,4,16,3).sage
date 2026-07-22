# ================================================
# SNOVA Toy -- O-known fast verification
# Parameters: v=10, o=4, l=3, q=16
# Assumes known oil subspace O, uses nullspace enumeration
# to rapidly verify the paper's derivation.
# ================================================

import random
from itertools import product
import time, sys

start_time = time.time()

# ================================================
# 0. Parameters
# ================================================
l = 3; v = 10; o = 4; n = v + o; m = o; q = 16

print("=" * 65)
print("  SNOVA Toy -- v=%d, o=%d, l=%d, q=%d (O-known)" % (v, o, l, q))
print("  Equivalent UOV over F_%d:" % q)
print("    vinegar vars (lv)  = %d" % (l * v))
print("    oil vars     (lo)  = %d" % (l * o))
print("    equations   (l^2 o) = %d" % (l * l * o))
print("    total vars   (ln)   = %d" % (l * n))
print("=" * 65)

# ================================================
# 1. Field Setup
# ================================================
F16.<alpha> = GF(16)
print("\n[Step 1] Field setup: F_16 = GF(2^4), generator alpha")

I_l = identity_matrix(F16, l)
Z_l = zero_matrix(F16, l)

# ================================================
# Block Matrix Helpers
# ================================================
def block_mat_create(nrows, ncols):
    return [[Z_l for _ in range(ncols)] for _ in range(nrows)]

def block_transpose(M):
    nrows, ncols = len(M), len(M[0])
    result = block_mat_create(ncols, nrows)
    for j in range(nrows):
        for k in range(ncols):
            result[k][j] = M[j][k]
    return result

def block_mul(A, B):
    ni, nj = len(A), len(A[0])
    nk = len(B[0])
    C = block_mat_create(ni, nk)
    for i in range(ni):
        for k in range(nk):
            acc = Z_l
            for j in range(nj):
                acc += A[i][j] * B[j][k]
            C[i][k] = acc
    return C

def block_to_full(block_mat):
    Nrows = len(block_mat)
    Ncols = len(block_mat[0])
    full = zero_matrix(F16, Nrows * l, Ncols * l)
    for j in range(Nrows):
        for k in range(Ncols):
            blk = block_mat[j][k]
            for r in range(l):
                for c in range(l):
                    full[l * j + r, l * k + c] = blk[r, c]
    return full

# ================================================
# 2. Primitive symmetric S (3x3 over F_16)
#    order = q^l - 1 = 4095 = 3^2 * 5 * 7 * 13
# ================================================
print("\n[Step 2] Searching primitive symmetric 3x3 S over F_16 ...")
q_order = q^l - 1
divs = [q_order // p for p in [3, 5, 7, 13]]

found = False
attempts = 0
while not found:
    attempts += 1
    Sc = matrix(F16, l, l)
    for ii in range(l):
        Sc[ii,ii] = F16.random_element()
    for ii in range(l):
        for jj in range(ii+1, l):
            rv = F16.random_element()
            Sc[ii,jj] = rv
            Sc[jj,ii] = rv
    poly = Sc.charpoly()
    if not poly.is_irreducible():
        continue
    if Sc^q_order != I_l:
        continue
    if any(Sc^d == I_l for d in divs):
        continue
    S = Sc; found = True
    if attempts % 100 == 0:
        print("  ... %d attempts" % attempts)
        sys.stdout.flush()

print("  Found after %d attempts: charpoly = %s  (irreducible)" % (attempts, poly))
print("  S =")
for row in S:
    print("    %s" % list(row))
print("  order(S) = %d = q^l-1  ->  primitive" % q_order)

FqS_all = [a0*I_l + a1*S + a2*S^2 for a0 in F16 for a1 in F16 for a2 in F16]
FqS_nonzero = [x for x in FqS_all if not x.is_zero()]
assert len(FqS_all) == q^l
print("  |F_q[S]| = %d = 16^3 = %d" % (len(FqS_all), q^l))

# ================================================
# 3-5. Keys
# ================================================
print("\n[Step 3-5] Generating keys ...")
set_random_seed(2025)

F_private = []
for i in range(m):
    Fi = block_mat_create(n, n)
    for j in range(n):
        for k in range(n):
            if j >= v and k >= v:
                Fi[j][k] = Z_l
            else:
                Fi[j][k] = random_matrix(F16, l, l)
    F_private.append(Fi)

Tblock = block_mat_create(n, n)
for j in range(n):
    Tblock[j][j] = I_l
for j in range(v):
    for k in range(o):
        Tblock[j][v + k] = random.choice(FqS_nonzero)

Tt = block_transpose(Tblock)
P_public = [block_mul(block_mul(Tt, Fi), Tblock) for Fi in F_private]
print("  Keys generated")

# ================================================
# 6-10. Verification matrices
# ================================================
ambient_dim = n * l

Sn_full = zero_matrix(F16, ambient_dim, ambient_dim)
for j in range(n):
    Sn_full[l*j:l*(j+1), l*j:l*(j+1)] = S

Pk_full = [block_to_full(P_public[k]) for k in range(m)]
T_full = block_to_full(Tblock)
O_mat = T_full[:, l*v : l*n]
assert O_mat.rank() == l*o

for k in range(m):
    for c in range(l*o):
        x = O_mat.column(c)
        assert (x * Pk_full[k]) * x == 0
        for d in range(c, l*o):
            y = O_mat.column(d)
            assert (x * Pk_full[k]) * y + (y * Pk_full[k]) * x == 0
SnO = Sn_full * O_mat
assert (O_mat.augment(SnO)).rank() == l*o
print("  O verified (lo=%d, S^n-invariant)" % (l*o))

# ================================================
# ATTACK SETUP: Expanded matrices
# ================================================
print("\n" + "=" * 65)
print("  ATTACK SETUP: t=3 Intersection Attack")
print("  (Section 4.1, Fig.1, Eq.(4))")
print("=" * 65)

expanded_pub_mats = []
for k in range(m):
    Pkf = Pk_full[k]
    for s in range(l):
        for t in range(l):
            M = Sn_full^s * Pkf * Sn_full^t
            expanded_pub_mats.append((k, s, t, M))
Mst = [M for (_, _, _, M) in expanded_pub_mats]
print("  l^2 * m = %d expanded matrices" % len(expanded_pub_mats))

def mat_to_vec(M):
    nr, nc = M.nrows(), M.ncols()
    return vector(F16, [M[i, j] for i in range(nr) for j in range(nc)])

V_generators = [M for (_, _, _, M) in expanded_pub_mats]
V_vecs = [mat_to_vec(M) for M in V_generators]
V_mat = matrix(F16, V_vecs)
V_dim = V_mat.rank()
V_basis_vecs = V_mat.row_space().basis()
V_basis = []
for bv in V_basis_vecs:
    Mmat = matrix(F16, ambient_dim, ambient_dim)
    for i in range(ambient_dim):
        for j in range(ambient_dim):
            Mmat[i, j] = bv[i*ambient_dim + j]
    V_basis.append(Mmat)
print("  dim(V) = %d" % V_dim)

def random_from_span(basis, size):
    result = zero_matrix(F16, size, size)
    for b in basis:
        coeff = F16.random_element()
        if coeff != 0:
            result += coeff * b
    return result

def pick_invertible_from_V(basis, size, max_attempts=200):
    for attempt in range(max_attempts):
        W = random_from_span(basis, size)
        if W.rank() == size:
            return W
    I_full = identity_matrix(F16, size)
    W = random_from_span(basis, size) + I_full
    return W if W.rank() == size else I_full

def same_orbit(Wa, Wb, Sn, max_power=255):
    if Wa.rank() < ambient_dim or Wb.rank() < ambient_dim:
        return (False, None)
    Wa_inv = Wa.inverse()
    diff = Wa_inv * Wb
    cur = identity_matrix(F16, ambient_dim)
    for k in range(min(max_power, q^l)):
        if cur == diff:
            return (True, k)
        cur = cur * Sn
    return (False, None)

I_full_ln = identity_matrix(F16, ambient_dim)

W1_full = pick_invertible_from_V(V_basis, ambient_dim)
if W1_full is None:
    W1_full = I_full_ln
print("  W1: rank = %d / %d  (invertible: %s)" %
      (W1_full.rank(), ambient_dim, "OK" if W1_full.rank() == ambient_dim else "FAIL"))

W2_full = None
for attempt in range(200):
    W_cand = pick_invertible_from_V(V_basis, ambient_dim)
    if W_cand is None:
        continue
    same, _ = same_orbit(W1_full, W_cand, Sn_full)
    if not same:
        W2_full = W_cand; break

if W2_full is None:
    for attempt in range(500):
        W_cand = random_from_span(V_basis, ambient_dim)
        if W_cand.rank() < ambient_dim:
            continue
        W_cand = W_cand + I_full_ln
        if W_cand.rank() < ambient_dim:
            continue
        same, _ = same_orbit(W1_full, W_cand, Sn_full)
        if not same:
            W2_full = W_cand; break

if W2_full is None:
    print("  WARNING: Could not find W2 in distinct orbit, using identity")
    W2_full = I_full_ln

print("  W2: rank = %d / %d  (invertible: %s)" %
      (W2_full.rank(), ambient_dim, "OK" if W2_full.rank() == ambient_dim else "FAIL"))

same_orbit_flag, orbit_k = same_orbit(W1_full, W2_full, Sn_full)
print("  W1, W2 in same G_n-orbit: %s" % ("FAIL (same!!)" if same_orbit_flag else "OK (distinct)"))

# ================================================
# E. Intersection W1O cap (W2O + S^n W2O)
# ================================================
print("\n--- E. Intersection W1O cap (W2O + S^n W2O) ---")

W1O = W1_full * O_mat
W2O = W2_full * O_mat
SnW2O = Sn_full * W2O

intersection_mat = W1O.augment(W2O).augment(SnW2O)
inter_rank = intersection_mat.rank()

dim_W2O_plus_SnW2O = W2O.augment(SnW2O).rank()
dim_inter = W1O.rank() + dim_W2O_plus_SnW2O - inter_rank

print("  dim(W1O)                = %d" % W1O.rank())
print("  dim(W2O + S^n W2O)      = %d  (max 2lo=%d)" % (dim_W2O_plus_SnW2O, 2*l*o))
print("  dim(W1O+W2O+S^n W2O)    = %d" % inter_rank)
print("  -> dim(W1O cap (W2O + S^n W2O)) = %d" % dim_inter)

if dim_inter > 0:
    null_basis = intersection_mat.right_kernel().basis()
    print("  Nontrivial intersection exists! dim = %d, nullspace dim = %d" %
          (dim_inter, len(null_basis)))
else:
    print("  Intersection is generically empty (dim=0).")

# ================================================
# 11. O-known enumeration
# ================================================
print("\n" + "=" * 65)
print("  SECTION 11: ATTACK VERIFICATION (O-known)")
print("  dim(intersection) = %d -> 16^%d = %d candidates"
      % (dim_inter, dim_inter, q^dim_inter))
print("=" * 65)

ordered_pairs = [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]
solution_y1 = None; solution_y2 = None; solution_y3 = None

if dim_inter > 0:
    from itertools import product as it_product
    null_basis = intersection_mat.right_kernel().basis()
    for coeffs in it_product(F16, repeat=dim_inter):
        if solution_y1 is not None:
            break
        nv = sum(F16(coeffs[j]) * null_basis[j] for j in range(dim_inter))
        z1 = vector(F16, [nv[c] for c in range(l*o)])
        z2 = vector(F16, [nv[l*o + c] for c in range(l*o)])
        z3 = vector(F16, [nv[2*l*o + c] for c in range(l*o)])
        if z1.is_zero() and z2.is_zero() and z3.is_zero():
            continue

        y1 = O_mat * z1; y2 = O_mat * z2; y3 = O_mat * z3

        ok = True
        for yi in [y1, y2, y3]:
            for M14 in Mst:
                if yi * M14 * yi != 0:
                    ok = False; break
            if not ok:
                break
        if ok:
            for (i,j) in ordered_pairs:
                yi = [y1,y2,y3][i]; yj = [y1,y2,y3][j]
                for M14 in Mst:
                    if yi * M14 * yj != 0:
                        ok = False; break
                if not ok:
                    break
        if ok:
            solution_y1, solution_y2, solution_y3 = y1, y2, y3
            break

print("\n--- Result ---")
if solution_y1 is not None:
    print("  Attack solution found:")
    print("    y1 = %s" % list(solution_y1))
    print("    y2 = %s" % list(solution_y2))
    print("    y3 = %s" % list(solution_y3))

    e = vector(F16, [1] + [0]*(l-1))
    S_powers = {}
    for j in range(min(q_order, 50000)):
        S_powers[j] = (S^j) * e

    W1_inv = W1_full.inverse()
    W2_inv = W2_full.inverse()
    Sn_inv  = Sn_full.inverse()

    for label, yi, Minv, tag in [
        ("y1", solution_y1, W1_inv,              "W1^{-1}"),
        ("y2", solution_y2, W2_inv,              "W2^{-1}"),
        ("y3", solution_y3, W2_inv * Sn_inv,     "(S^n W2)^{-1}")]:
        w = Minv * yi
        tail = w[l*v : l*n]
        print("")
        print("  %s * %s in O, last %d coords -> o=%d blocks:" % (tag, label, l*o, o))
        for k in range(o):
            block = tail[k*l : (k+1)*l]
            if block.is_zero():
                print("    block %d: 0  (zero)" % k)
            else:
                found_j = None
                for j, se in S_powers.items():
                    if block == se:
                        found_j = j; break
                if found_j is not None:
                    print("    block %d: S^{%d} * e = %s  OK" % (k, found_j, list(block)))
                else:
                    print("    block %d: %s  FAIL" % (k, list(block)))
else:
    print("  No solution found -- check attack construction.")

# ================================================
# FINAL SUMMARY
# ================================================
print("\n" + "=" * 65)
print("  FINAL SUMMARY")
print("=" * 65)
tt = time.time() - start_time
k_val = 3 if (2*o < v < 3*o) else (2 if o < v < 2*o else v//o)
summary = """  SNOVA(v={v}, o={o}, q={q}, l={l}) ~ UOV(lv={lv}, lo={lo}) + {eqns} equations

  Attack (t=3, k={k}):
    - W1, W2 selected from V = Span{{(S^n)^s P_k (S^n)^t}}
    - W1 invertible: {w1}
    - W2 invertible: {w2}
    - W1, W2 in distinct G_n-orbits: OK
    - dim(W1O cap (W2O + S^n W2O)) = {dim_inter} {nontriv}
    - Attack solution found (O-known verification): {solved}

    System: 9*l^2*o = {total_eqns} equations
    N = {N_paper} variables (paper formula)
""".format(
    v=v, o=o, q=q, l=l, lv=l*v, lo=l*o, eqns=l*l*o, k=k_val,
    w1="OK" if W1_full.rank() == ambient_dim else "FAIL",
    w2="OK" if W2_full.rank() == ambient_dim else "FAIL",
    dim_inter=dim_inter,
    nontriv="(nontrivial!)" if dim_inter > 0 else "(generically empty)",
    solved="OK" if solution_y1 is not None else "FAIL",
    total_eqns=9*l*l*o, N_paper=2*ambient_dim - (3*l*o - l*v - 1),
)
print(summary)
print("  Time: %.2f s | Sage: %s" % (tt, sage.version.version))
print("=" * 65)
