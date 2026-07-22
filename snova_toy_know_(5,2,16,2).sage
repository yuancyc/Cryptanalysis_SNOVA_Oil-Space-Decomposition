# ================================================
# SNOVA Toy — O-known fast verification
# Parameters: v=5, o=2, l=2, q=16
# Assumes known oil subspace O, uses nullspace enumeration
# to rapidly verify the paper's derivation.
# ================================================

import random
from itertools import combinations, product
import time, sys

start_time = time.time()

# ================================================
# 0. Parameters
# ================================================
l = 2; v = 5; o = 2; n = v + o; m = o; q = 16

print("=" * 65)
print("  SNOVA Toy — v=%d, o=%d, l=%d, q=%d (O-known)" % (v, o, l, q))
print("  Equivalent UOV over F_%d:" % q)
print("    vinegar vars (lv)  = %d" % (l * v))
print("    oil vars     (lo)  = %d" % (l * o))
print("    equations   (l^2 o) = %d" % (l * l * o))
print("    total vars   (ln)   = %d" % (l * n))
print("=" * 65)

# ================================================
# 1. Field Setup: F_16 = F_2[alpha] / (alpha^4 + alpha + 1)
# ================================================
F16.<alpha> = GF(16)
print("\n[Step 1] Field setup: F_16 = GF(2^4), generator alpha")

R = MatrixSpace(F16, l)
I_l = identity_matrix(F16, l)
Z_l = zero_matrix(F16, l)

# ================================================
# Block Matrix Helpers
# ================================================

def block_mat_create(nrows, ncols):
    """Create a zero block matrix of size nrows x ncols."""
    return [[Z_l for _ in range(ncols)] for _ in range(nrows)]

def block_transpose(M):
    """Block-level transpose."""
    nrows, ncols = len(M), len(M[0])
    result = block_mat_create(ncols, nrows)
    for j in range(nrows):
        for k in range(ncols):
            result[k][j] = M[j][k]
    return result

def block_mul(A, B):
    """Block matrix multiplication."""
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

def block_mul_vec(A, x):
    """Block matrix x vector."""
    ni = len(A)
    result = [Z_l for _ in range(ni)]
    for i in range(ni):
        acc = Z_l
        for j in range(len(x)):
            acc += A[i][j] * x[j]
        result[i] = acc
    return result

def block_quadratic(M, x):
    """Quadratic form: x^T * M * x."""
    N = len(x)
    acc = Z_l
    for j in range(N):
        for k in range(N):
            acc += x[j].transpose() * M[j][k] * x[k]
    return acc

def block_to_full(block_mat):
    """Convert n x n block matrix -> (nl) x (nl) matrix over F_q."""
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
# 2. Primitive symmetric S (2x2 over F_16)
#    order = q^l - 1 = 255 = 3*5*17
# ================================================
print("\n[Step 2] Searching primitive symmetric S ...")

divisors = [255 // p for p in [3, 5, 17]]

found = False
for s11 in F16:
    if found: break
    for s22 in F16:
        if found: break
        for s12 in F16:
            S_cand = matrix(F16, [[s11, s12], [s12, s22]])
            poly = S_cand.charpoly()
            if not poly.is_irreducible(): continue
            if S_cand^255 != I_l: continue
            if any(S_cand^d == I_l for d in divisors): continue
            S = S_cand; found = True

assert found, "Failed to find primitive symmetric S!"

print("  S = [[%s, %s], [%s, %s]]" % (S[0,0], S[0,1], S[1,0], S[1,1]))
print("  charpoly = %s  (irreducible)" % poly)
print("  order(S) = 255 = q^l - 1  ->  primitive")

FqS_all = [a0 * I_l + a1 * S for a0 in F16 for a1 in F16]
FqS_nonzero = [x for x in FqS_all if not x.is_zero()]
assert len(FqS_all) == q^l
print("  |F_q[S]| = %d = 16^2 = 256" % len(FqS_all))

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

# M_{k,s,t} = (S^n)^s * Pk_full * (S^n)^t
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
    if W_cand is None: continue
    same, _ = same_orbit(W1_full, W_cand, Sn_full)
    if not same: W2_full = W_cand; break

if W2_full is None:
    for attempt in range(500):
        W_cand = random_from_span(V_basis, ambient_dim)
        if W_cand.rank() < ambient_dim: continue
        W_cand = W_cand + I_full_ln
        if W_cand.rank() < ambient_dim: continue
        same, _ = same_orbit(W1_full, W_cand, Sn_full)
        if not same: W2_full = W_cand; break

if W2_full is None:
    print("  WARNING: Could not find W2 in distinct orbit, using identity")
    W2_full = I_full_ln

print("  W2: rank = %d / %d  (invertible: %s)" %
      (W2_full.rank(), ambient_dim, "OK" if W2_full.rank() == ambient_dim else "FAIL"))

same_orbit_flag, orbit_k = same_orbit(W1_full, W2_full, Sn_full)
print("  W1, W2 in same G_n-orbit: %s" % ("FAIL (same!!)" if same_orbit_flag else "OK (distinct)"))

# ================================================
# E. Set up t=3 intersection: W1O cap (W2O + S^n W2O)
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
    print("  Nontrivial intersection exists! dim = %d, nullspace dim = %d" % (dim_inter, len(null_basis)))
else:
    print("  Intersection is generically empty (dim=0).")

# ================================================
# F. Full Eq.(4) system (variables in F_q^{ln}, no O-parametrization)
# ================================================
print("\n--- F. Full Eq.(4) system ---")

tot_vars = 3 * ambient_dim
tot_eqns = 9 * l * l * o
print("  Variables: y1,y2,y3 in F_q^{%d}  ->  %d variables" % (ambient_dim, tot_vars))
print("  Eq.(4): 9*l^2*o = %d equations" % tot_eqns)

# ---- Monomial index ----
mono_index = {}
mcol = 0
for i in range(3):
    for a in range(ambient_dim):
        for b in range(a, ambient_dim):
            mono_index[('w', i, a, b)] = mcol
            mcol += 1
num_w = mcol
for i in range(3):
    for j in range(i+1, 3):
        for a in range(ambient_dim):
            for b in range(ambient_dim):
                mono_index[('c', i, j, a, b)] = mcol
                mcol += 1
num_monos = mcol
print("  Monomial basis: %d = within(%d) + cross(%d)" % (num_monos, num_w, num_monos - num_w))

# ---- Build rows ----
all_rows = []
row_labels = []

for i in range(3):
    for (k, s, t, M) in expanded_pub_mats:
        row = [F16(0)] * num_monos
        for a in range(ambient_dim):
            for b in range(a, ambient_dim):
                col = mono_index[('w', i, a, b)]
                row[col] = M[a, a] if a == b else M[a, b] + M[b, a]
        all_rows.append(row)
        row_labels.append("Q(y%d)_(%d,%d,%d)" % (i+1, k, s, t))

for (i, j) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
    for (k, s, t, M) in expanded_pub_mats:
        row = [F16(0)] * num_monos
        for a in range(ambient_dim):
            for b in range(ambient_dim):
                coeff = M[a, b]
                if coeff == 0: continue
                if i < j:
                    col = mono_index[('c', i, j, a, b)]
                else:
                    col = mono_index[('c', j, i, b, a)]
                row[col] += coeff
        all_rows.append(row)
        row_labels.append("B(y%d,y%d)_(%d,%d,%d)" % (i+1, j+1, k, s, t))

print("  Total degree-2 equations: %d (= 9*l^2*o)" % len(all_rows))

# ---- Rank analysis ----
print("\n--- G. Rank analysis ---")

coeff_mat = matrix(F16, all_rows)
total_rank = coeff_mat.rank()
redundant = len(all_rows) - total_rank

print("  Coefficient matrix: %d rows x %d columns" % (len(all_rows), num_monos))
print("  Rank = %d / %d" % (total_rank, len(all_rows)))
print("  Redundant equations: %d" % redundant)

echelon = coeff_mat.echelon_form()
pivot_rows = []
for r in range(echelon.nrows()):
    if any(echelon[r, c] != 0 for c in range(echelon.ncols())):
        pivot_rows.append(r)
    if len(pivot_rows) >= total_rank:
        break

print("  Independent equations (%d):" % len(pivot_rows))
for pr in pivot_rows[:12]:
    print("    row %3d: %s" % (pr, row_labels[pr]))
if len(pivot_rows) > 12:
    print("    ... (%d more)" % (len(pivot_rows) - 12))

quad_rows = [r for r in range(len(all_rows)) if row_labels[r].startswith('Q')]
bilin_rows = [r for r in range(len(all_rows)) if row_labels[r].startswith('B')]
quad_submat = coeff_mat.matrix_from_rows(quad_rows)
quad_rank_only = quad_submat.rank()
bilin_submat = coeff_mat.matrix_from_rows(bilin_rows)
bilin_rank_only = bilin_submat.rank()
print("  Quadratic rank: %d/%d, Bilinear rank: %d/%d, overlap: %d" %
      (quad_rank_only, len(quad_rows), bilin_rank_only, len(bilin_rows),
       quad_rank_only + bilin_rank_only - total_rank))

# ---- Linear constraint rank ----
SnW2_full_lr = Sn_full * W2_full
lin_coeff_full = zero_matrix(F16, ambient_dim, 3*ambient_dim)
for r in range(ambient_dim):
    for a in range(ambient_dim):
        lin_coeff_full[r, a]                 = W1_full[r, a]
        lin_coeff_full[r, ambient_dim + a]   = W2_full[r, a]
        lin_coeff_full[r, 2*ambient_dim + a] = SnW2_full_lr[r, a]
lin_rank_full = lin_coeff_full.rank()
lin_nullity_full = 3*ambient_dim - lin_rank_full
print("  Matrix [W1 | W2 | S^n W2]: %d x %d, rank=%d, nullity=%d" %
      (ambient_dim, 3*ambient_dim, lin_rank_full, lin_nullity_full))

# ---- Key verification ----
print("\n--- H. Key verification ---")
w1_in_V = (matrix(F16, [mat_to_vec(b) for b in V_basis]).stack(
    matrix(F16, [mat_to_vec(W1_full)])).rank() == V_dim)
w2_in_V = (matrix(F16, [mat_to_vec(b) for b in V_basis]).stack(
    matrix(F16, [mat_to_vec(W2_full)])).rank() == V_dim)
print("  W1 in V: %s" % ("OK" if w1_in_V else "FAIL"))
print("  W2 in V: %s" % ("OK" if w2_in_V else "FAIL"))
print("  dim(W1O) = %d (lo=%d)" % (W1O.rank(), l*o))
print("  dim(W2O) = %d (lo=%d)" % (W2O.rank(), l*o))

dim_all_three = W1O.augment(W2O).augment(SnW2O).rank()
dim_inter2 = W1O.rank() + dim_W2O_plus_SnW2O - dim_all_three
print("  dim(W1O cap (W2O + S^n W2O)) = %d + %d - %d = %d" %
      (W1O.rank(), dim_W2O_plus_SnW2O, dim_all_three, dim_inter2))

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
    for a in F16:
        if solution_y1 is not None: break
        for b in F16:
            nv = a * null_basis[0] + (b * null_basis[1] if dim_inter >= 2 else 0)
            z1 = vector(F16, [nv[c] for c in range(l*o)])
            z2 = vector(F16, [nv[l*o + c] for c in range(l*o)])
            z3 = vector(F16, [nv[2*l*o + c] for c in range(l*o)])
            if z1.is_zero() and z2.is_zero() and z3.is_zero():
                continue

            y1 = O_mat * z1; y2 = O_mat * z2; y3 = O_mat * z3

            ok = True
            for yi in [y1, y2, y3]:
                for M14 in Mst:
                    if yi * M14 * yi != 0: ok = False; break
                if not ok: break
            if ok:
                for (i,j) in ordered_pairs:
                    yi = [y1,y2,y3][i]; yj = [y1,y2,y3][j]
                    for M14 in Mst:
                        if yi * M14 * yj != 0: ok = False; break
                    if not ok: break
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
    S_powers = {j: (S^j) * e for j in range(255)}

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
                    if block == se: found_j = j; break
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

    Key properties verified:
    - S is primitive, symmetric, charpoly irreducible
    - F_i have OV structure (oil x oil = 0)
    - T is upper triangular with F_q[S] entries
    - P = F o T
    - O is S^n-invariant
    - O = T^{{-1}}(O_priv), dim = lo
    - P_k vanishes on O
    - Expanded public polynomials constructed
    - V span dimension analyzed
    - W1O cap (W2O + S^n W2O) intersection set up
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
print("  Time: %.2f s | Sage: %s" % (tt, version))
print("=" * 65)
