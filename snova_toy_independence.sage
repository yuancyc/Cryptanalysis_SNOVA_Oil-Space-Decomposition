# ============================================================
# SNOVA: Independence verification of quadratic equations
# after eliminating y0 from System (4)
# ============================================================

import random
from collections import defaultdict

def mat_to_vec(M):
    nr, nc = M.nrows(), M.ncols()
    return vector(M.base_ring(), [M[i, j] for i in range(nr) for j in range(nc)])

def block_mat_create(nrows, ncols, Z):
    return [[Z for _ in range(ncols)] for _ in range(nrows)]

def block_transpose(M):
    nrows, ncols = len(M), len(M[0])
    result = block_mat_create(ncols, nrows, M[0][0].parent().zero())
    for j in range(nrows):
        for k in range(ncols):
            result[k][j] = M[j][k]
    return result

def block_mul(A, B):
    ni, nj = len(A), len(A[0]); nk = len(B[0])
    Z = A[0][0].parent().zero()
    C = block_mat_create(ni, nk, Z)
    for i in range(ni):
        for k in range(nk):
            acc = Z
            for j in range(nj):
                acc += A[i][j] * B[j][k]
            C[i][k] = acc
    return C

def block_to_full(block_mat, Fq, L):
    Nrows, Ncols = len(block_mat), len(block_mat[0])
    full = matrix(Fq, Nrows * L, Ncols * L)
    for j in range(Nrows):
        rbase = L * j
        for k in range(Ncols):
            cbase = L * k
            blk = block_mat[j][k]
            for r in range(L):
                for c in range(L):
                    full[rbase + r, cbase + c] = blk[r, c]
    return full

def mat_to_int_packed(M, q, elem_to_int):
    val = 0
    for i in range(M.nrows()):
        for j in range(M.ncols()):
            val = val * q + elem_to_int[M[i, j]]
    return val

def precompute_S_powers_set(S, q, ell, elem_to_int):
    Fq = S.base_ring()
    order = q**ell - 1
    s_set = set()
    cur = identity_matrix(Fq, ell)
    for _ in range(order):
        s_set.add(mat_to_int_packed(cur, q, elem_to_int))
        cur = cur * S
    return s_set

def sn_full_mul_left(S_pow, M_in, ell, n):
    M = M_in.__copy__()
    for i in range(n):
        rs = slice(ell*i, ell*(i+1))
        M[rs, :] = S_pow * M_in[rs, :]
    return M

def sn_full_mul_right(M_in, S_pow, ell, n):
    M = M_in.__copy__()
    for j in range(n):
        cs = slice(ell*j, ell*(j+1))
        M[:, cs] = M_in[:, cs] * S_pow
    return M

def check_snova(v, o, ell, q, seed=None):
    if seed is not None:
        set_random_seed(seed)

    Fq = GF(q)
    Iell = identity_matrix(Fq, ell)
    Zell = zero_matrix(Fq, ell)
    n = v + o
    ln = ell * n
    t = ell + 1
    elem_to_int = {e: i for i, e in enumerate(Fq)}

    # Generate primitive symmetric S
    S = None
    while S is None:
        entries = [Fq.random_element() for _ in range(ell*(ell+1)//2)]
        Mtmp = matrix(Fq, ell, ell)
        idx = 0
        for i in range(ell):
            for j in range(i, ell):
                Mtmp[i,j] = entries[idx]
                if i != j:
                    Mtmp[j,i] = entries[idx]
                idx += 1
        if Mtmp.charpoly().is_irreducible():
            S = Mtmp

    S_pows = [identity_matrix(Fq, ell)]
    curS = S
    for _ in range(1, ell):
        S_pows.append(curS)
        curS = curS * S
    S_powers_set = precompute_S_powers_set(S, q, ell, elem_to_int)

    def random_FqS_element(nonzero=False):
        while True:
            coeffs = [Fq.random_element() for _ in range(ell)]
            mat = sum(coeffs[i] * S_pows[i] for i in range(ell))
            if not nonzero or not mat.is_zero():
                return mat

    # Private key generation
    m = o
    F_private = []
    for _ in range(m):
        Fi = block_mat_create(n, n, Zell)
        for j in range(n):
            for k in range(n):
                if j >= v and k >= v:
                    Fi[j][k] = Zell
                else:
                    Fi[j][k] = random_matrix(Fq, ell, ell)
        F_private.append(Fi)

    Tblock = block_mat_create(n, n, Zell)
    for j in range(n):
        Tblock[j][j] = Iell
    for j in range(v):
        for k in range(o):
            Tblock[j][v + k] = random_FqS_element(nonzero=True)

    Tt = block_transpose(Tblock)
    P_public = [block_mul(block_mul(Tt, Fi), Tblock) for Fi in F_private]

    # Expanded public matrices: (S^n)^s * P_k * (S^n)^t
    Pk_full = [block_to_full(P_public[k], Fq, ell) for k in range(m)]
    expanded_pub_mats = []
    for k in range(m):
        Pkf = Pk_full[k]
        for s in range(ell):
            left = Pkf if s == 0 else sn_full_mul_left(S_pows[s], Pkf, ell, n)
            for tau in range(ell):
                Mres = left if tau == 0 else sn_full_mul_right(left, S_pows[tau], ell, n)
                expanded_pub_mats.append((k, s, tau, Mres))
    pub_mat_list = [M for (_, _, _, M) in expanded_pub_mats]

    # V-span, W1, W2
    V_vecs = [mat_to_vec(M) for (_, _, _, M) in expanded_pub_mats]
    V_mat = matrix(Fq, V_vecs)
    V_basis_vecs = V_mat.row_space().basis()
    V_basis = []
    for bv in V_basis_vecs:
        Mmat = matrix(Fq, ln, ln)
        for i in range(ln):
            for j in range(ln):
                Mmat[i, j] = bv[i*ln + j]
        V_basis.append(Mmat)

    def random_from_span(basis, size):
        result = zero_matrix(Fq, size, size)
        for b in basis:
            coeff = Fq.random_element()
            if coeff != 0:
                result += coeff * b
        return result

    def pick_invertible(basis, size, max_attempts=500):
        I_full = identity_matrix(Fq, size)
        for _ in range(max_attempts):
            W = random_from_span(basis, size)
            if W.rank() == size:
                return W
        W = random_from_span(basis, size) + I_full
        if W.rank() == size:
            return W
        return I_full

    def same_orbit(Wa, Wb):
        if Wa.rank() < ln or Wb.rank() < ln:
            return False
        diff = Wa.inverse() * Wb
        first_block_int = None
        for i in range(n):
            r0 = ell * i
            block = diff[r0:r0+ell, r0:r0+ell]
            val = 0
            for ri in range(ell):
                for ci in range(ell):
                    val = val * q + elem_to_int[block[ri, ci]]
            if val not in S_powers_set:
                return False
            if first_block_int is None:
                first_block_int = val
            elif val != first_block_int:
                return False
        for i in range(n):
            r0 = ell * i
            for j in range(n):
                if i == j:
                    continue
                c0 = ell * j
                if not diff[r0:r0+ell, c0:c0+ell].is_zero():
                    return False
        return True

    W1_full = pick_invertible(V_basis, ln)
    W2_full = None
    w2_fallback = False
    w2_attempts = 0
    for _ in range(500):
        w2_attempts += 1
        Wc = pick_invertible(V_basis, ln)
        if not same_orbit(W1_full, Wc):
            W2_full = Wc
            break
    if W2_full is None:
        W2_full = identity_matrix(Fq, ln)
        w2_fallback = True

    same_orb = same_orbit(W1_full, W2_full)

    # A_j = W1^{-1} * (I_n (x) S^{j-1}) * W2
    W1_inv = W1_full.inverse()
    A_blocks = []
    for j in range(1, t):
        if j-1 == 0:
            A_blocks.append(W1_inv * W2_full)
        else:
            A_blocks.append(W1_inv * sn_full_mul_left(S_pows[j-1], W2_full, ell, n))

    num_eqns = t * t * ell * ell * o
    N = ln

    # Monomial index for z = [y1, ..., y_ell]
    mono = {}
    mcol = 0
    for p in range(ell):
        for a in range(N):
            for b in range(a, N):
                mono[('w', p, a, b)] = mcol
                mcol += 1
    for p in range(ell):
        for q in range(p+1, ell):
            for a in range(N):
                for b in range(N):
                    mono[('c', p, q, a, b)] = mcol
                    mcol += 1
    num_monos = mcol

    # Add bilinear form z_u^T X z_v to row
    def add_bilinear(row, u, v, X):
        if u == v:
            for a in range(N):
                c = X[a, a]
                if c != 0:
                    row[mono[('w', u, a, a)]] += c
                for b in range(a+1, N):
                    c = X[a, b] + X[b, a]
                    if c != 0:
                        row[mono[('w', u, a, b)]] += c
        elif u < v:
            for a in range(N):
                for b in range(N):
                    c = X[a, b]
                    if c != 0:
                        row[mono[('c', u, v, a, b)]] += c
        else:  # u > v
            for a in range(N):
                for b in range(N):
                    c = X[a, b]
                    if c != 0:
                        row[mono[('c', v, u, b, a)]] += c

    # Build coefficient matrix by direct substitution
    # y0 = sum_{p=1}^{ell} A_p * y_p
    # After elimination: z = [y1, ..., y_ell], z_{p-1} = y_p
    all_rows = []
    for M in pub_mat_list:
        for i in range(t):
            for j in range(t):
                row = [Fq(0)] * num_monos

                if i >= 1 and j >= 1:
                    add_bilinear(row, i-1, j-1, M)

                elif i == 0 and j >= 1:
                    for p in range(1, t):
                        ApT_M = A_blocks[p-1].transpose() * M
                        add_bilinear(row, p-1, j-1, ApT_M)

                elif i >= 1 and j == 0:
                    for q in range(1, t):
                        M_Aq = M * A_blocks[q-1]
                        add_bilinear(row, i-1, q-1, M_Aq)

                else:  # i == 0 and j == 0
                    for p in range(1, t):
                        ApT_M = A_blocks[p-1].transpose() * M
                        for q in range(1, t):
                            ApT_M_Aq = ApT_M * A_blocks[q-1]
                            add_bilinear(row, p-1, q-1, ApT_M_Aq)

                all_rows.append(row)

    coeff_mat = matrix(Fq, all_rows)
    rank_val = coeff_mat.rank()

    # Left kernel analysis: find redundant equation structure
    left_kernel = coeff_mat.left_kernel().basis()

    # Map each row index back to (M_idx, i, j)
    row_info = []
    for M_idx in range(len(pub_mat_list)):
        for i in range(t):
            for j in range(t):
                row_info.append((M_idx, i, j))

    kernel_analysis = []
    for kv in left_kernel:
        involved = []
        for r in range(len(kv)):
            if kv[r] != 0:
                M_idx, i, j = row_info[r]
                involved.append((kv[r], M_idx, i, j))
        by_ij = defaultdict(list)
        for (coeff, M_idx, i, j) in involved:
            by_ij[(i,j)].append((coeff, M_idx))
        kernel_analysis.append({
            'num_terms': len(involved),
            'by_ij': dict(by_ij),
            'ij_pairs': sorted(by_ij.keys()),
        })

    return {
        'v': v, 'o': o, 'ell': ell, 'q': q,
        't': t, 'N': N, 'D': ell * N,
        'num_eqns': num_eqns,
        'num_monos': num_monos,
        'rank': rank_val,
        'deficit': num_eqns - rank_val,
        'w2_fallback': w2_fallback,
        'w2_attempts': w2_attempts,
        'same_orbit': same_orb,
        'V_dim': V_mat.rank(),
        'kernel_dim': len(left_kernel),
        'kernel_analysis': kernel_analysis,
    }

# ============================================================
# Main
# ============================================================
MAX_AMBIENT = 80

print("=" * 90)
print("  SNOVA: Quadratic Equation Independence after y0 Elimination")
print("  Constraint: y0 = sum_j W1^{-1} S^{j-1} W2 y_j")
print("  Equations: z^T (A_i^T M A_j) z = 0,  total: t^2 * ell^2 * o")
print("  Method: direct term-by-term substitution")
print("=" * 90)

all_results = []
for ell_val in [2, 3, 4, 5]:
    t_val = ell_val + 1
    print("\n" + "-" * 90)
    print("  ell = %d  (t = %d,  t*ell = %d)" % (ell_val, t_val, t_val * ell_val))
    print("-" * 90)

    if ell_val == 5:
        param_sets = []
        for o_test in range(1, 5):
            for v_test in range(ell_val * o_test + 1, (ell_val + 1) * o_test):
                if ell_val * (v_test + o_test) <= MAX_AMBIENT:
                    param_sets.append((v_test, o_test))
        param_sets = param_sets[:3]
    else:
        param_sets = []
        for o_test in range(2, 8):
            for v_test in range(ell_val * o_test + 1, (ell_val + 1) * o_test):
                if ell_val * (v_test + o_test) <= MAX_AMBIENT:
                    param_sets.append((v_test, o_test))
        param_sets = param_sets[:5]

    if not param_sets:
        print("  (no valid parameter sets)")
        continue

    print("  %-10s %5s %5s %7s %7s %7s %7s"
          % ("(v,o)", "N", "D", "eqns", "monos", "rank", "deficit"))
    print("  " + "-" * 60)

    for (vv, oo) in param_sets:
        seed = 1000 * ell_val + 100 * vv + 10 * oo
        res = check_snova(vv, oo, ell_val, 16, seed=seed)
        all_results.append(res)
        print("  (v=%2d,o=%2d)  %5d %5d %7d %7d %7d %7d"
              % (vv, oo, res['N'], res['D'],
                 res['num_eqns'], res['num_monos'], res['rank'],
                 res['deficit']))

# Summary
print("\n" + "=" * 90)
print("  SUMMARY")
print("=" * 90)
print("  %3s %4s %3s %5s %5s %7s %7s %7s %7s %8s"
       % ("ell", "v", "o", "N", "D", "eqns", "rank", "deficit", "t*ell", "kernel_dim"))
print("  " + "-" * 85)
for r in all_results:
    print("  %3d %4d %3d %5d %5d %7d %7d %7d %7d %8d"
          % (r['ell'], r['v'], r['o'], r['N'], r['D'],
             r['num_eqns'], r['rank'], r['deficit'],
             r['t'] * r['ell'], r['kernel_dim']))

print("  " + "-" * 85)
deficit_ok = all(r['deficit'] == r['t'] * r['ell'] for r in all_results)
kernel_ok = all(r['kernel_dim'] == r['t'] * r['ell'] for r in all_results)
print("  deficit = t*ell  in all cases:  %s" % ("YES" if deficit_ok else "NO"))
print("  kernel_dim = t*ell in all cases: %s" % ("YES" if kernel_ok else "NO"))

# Kernel structure analysis (ell=2, first case only)
print("\n" + "=" * 90)
print("  Left Kernel Structure Analysis (ell=2, first parameter set)")
print("=" * 90)
r0 = all_results[0]
print("  (v=%d, o=%d):  deficit = %d,  kernel_dim = %d"
      % (r0['v'], r0['o'], r0['deficit'], r0['kernel_dim']))

kernel_by_i = defaultdict(list)
for ki, ka in enumerate(r0['kernel_analysis']):
    i_vals = set(ij[0] for ij in ka['ij_pairs'])
    for iv in i_vals:
        kernel_by_i[iv].append((ki, ka))

for iv in sorted(kernel_by_i.keys()):
    klist = kernel_by_i[iv]
    print("\n  --- i = %d  (%d kernel vectors) ---" % (iv, len(klist)))
    for ki, ka in klist:
        ij_str = ", ".join("(i=%d,j=%d):%dM" % (ij[0], ij[1], len(ka['by_ij'][ij]))
                           for ij in sorted(ka['by_ij'].keys()))
        print("    kernel[%d]: %d terms, %s" % (ki, ka['num_terms'], ij_str))

print("\n" + "=" * 90)
print("  DONE")
print("=" * 90)
