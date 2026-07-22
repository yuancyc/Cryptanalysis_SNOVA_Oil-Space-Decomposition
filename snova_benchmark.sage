# ============================================================
# SNOVA -- Small-Scale Attack Benchmark
# Runs the full M4GB attack on toy SNOVA parameters and
# produces a table of timings for the paper.
# ============================================================

import random, time, sys, os, re

# ============================================================
# M4GB path -- edit this to match your installation
# ============================================================
# M4GB_HOME = "/home/yuan/Desktop/m4gb"
M4GB_HOME = os.path.join(os.getcwd(), "m4gb")

# ============================================================
# Parameters: (v, o, q, l, label)
# ============================================================
BENCH_PARAMS = [
    (2, 1, 16, 2, "SNOVA(2,1,16,2)"),
    (2, 1, 16, 3, "SNOVA(2,1,16,3)"),
    (2, 1, 16, 4, "SNOVA(2,1,16,4)"),
    (4, 2, 16, 2, "SNOVA(4,2,16,2)"),
]

M4GB_TIMEOUT = 300   # seconds per M4GB run (5 min)
MAX_PINS    = 5      # random dehomogenization attempts
NUM_RUNS    = 5      # average over this many runs per parameter

results = []

def tprint(msg):
    print("    %s" % msg)
    sys.stdout.flush()

# ---- GF(16) <-> int ----
def gfi(e):
    bits = e.polynomial().list()
    n = 0
    for i, c in enumerate(bits):
        if c != 0: n |= (1 << i)
    return n

def int_to_f16(F16, alpha, n):
    el = F16(0)
    for i in range(4):
        if (n >> i) & 1:
            el += alpha**i
    return el

# ============================================================
def run_one(v, o, q, l, label, seed=2025):
    set_random_seed(seed)

    F16 = GF(q)
    alpha = F16.gen()
    I_l = identity_matrix(F16, l)
    Z_l = zero_matrix(F16, l)
    n_total = v + o
    m = o
    amb = n_total * l
    tot_vars = 3 * amb
    tot_eqns = 9 * l * l * o

    tprint("ambient=%d  full vars=%d" % (amb, tot_vars))

    # ---- Primitive symmetric S ----
    tprint("Finding primitive S (l=%d)..." % l)
    order_S = q**l - 1
    div_map = {2: [3,5,17], 3: [3,5,7,13], 4: [3,5,17,257]}
    divs = [order_S // p for p in div_map.get(l, [3,5])]

    S = None
    while S is None:
        if l == 2:
            a,b,c = [F16.random_element() for _ in range(3)]
            Sc = matrix(F16, [[a,c],[c,b]])
        else:
            Sc = matrix(F16, l, l)
            for i in range(l):
                Sc[i,i] = F16.random_element()
                for j in range(i+1, l):
                    rv = F16.random_element()
                    Sc[i,j] = rv; Sc[j,i] = rv
        poly = Sc.charpoly()
        if not poly.is_irreducible(): continue
        if Sc**order_S != I_l: continue
        if any(Sc**d == I_l for d in divs): continue
        S = Sc
    tprint("S found, order=%d" % order_S)

    # F_q[S] nonzero
    if l == 2:
        FqS_nz = [a0*I_l + a1*S for a0 in F16 for a1 in F16
                  if not (a0==0 and a1==0)]
    elif l == 3:
        FqS_nz = [a0*I_l + a1*S + a2*S**2
                  for a0 in F16 for a1 in F16 for a2 in F16
                  if not (a0==0 and a1==0 and a2==0)]
    else:
        Spows = [S**j for j in range(l)]
        def _rand_fqs_nz():
            while True:
                cf = [F16.random_element() for _ in range(l)]
                if any(c != 0 for c in cf):
                    return sum(cf[j]*Spows[j] for j in range(l))
        FqS_nz = None

    # ---- Block helpers ----
    def bm_new(nr, nc):
        return [[Z_l for _ in range(nc)] for _ in range(nr)]
    def bm_T(M):
        nr, nc = len(M), len(M[0])
        r = bm_new(nc, nr)
        for j in range(nr):
            for k in range(nc): r[k][j] = M[j][k]
        return r
    def bm_mul(A, B):
        ni, nj, nk = len(A), len(A[0]), len(B[0])
        C = bm_new(ni, nk)
        for i in range(ni):
            for k in range(nk):
                acc = Z_l
                for j in range(nj): acc += A[i][j] * B[j][k]
                C[i][k] = acc
        return C
    def bm_full(blk):
        nr, nc = len(blk), len(blk[0])
        full = zero_matrix(F16, nr*l, nc*l)
        for j in range(nr):
            for k in range(nc):
                for r in range(l):
                    for c in range(l):
                        full[l*j+r, l*k+c] = blk[j][k][r,c]
        return full

    # ---- Keys ----
    tprint("Generating keys...")
    F_priv = []
    for i in range(m):
        Fi = bm_new(n_total, n_total)
        for j in range(n_total):
            for k in range(n_total):
                if j >= v and k >= v: Fi[j][k] = Z_l
                else: Fi[j][k] = random_matrix(F16, l, l)
        F_priv.append(Fi)

    Tblk = bm_new(n_total, n_total)
    for j in range(n_total): Tblk[j][j] = I_l
    for j in range(v):
        for k in range(o):
            Tblk[j][v+k] = (random.choice(FqS_nz) if FqS_nz is not None
                            else _rand_fqs_nz())
    Tt = bm_T(Tblk)
    P_pub = [bm_mul(bm_mul(Tt, Fi), Tblk) for Fi in F_priv]

    # ---- S^n and expanded matrices ----
    Sn_full = zero_matrix(F16, amb, amb)
    for j in range(n_total): Sn_full[l*j:l*(j+1), l*j:l*(j+1)] = S
    Pk_full = [bm_full(P_pub[k]) for k in range(m)]

    tprint("Building expanded matrices...")
    expanded = []
    for k in range(m):
        for s in range(l):
            for t in range(l):
                M = Sn_full**s * Pk_full[k] * Sn_full**t
                expanded.append((k, s, t, M))
    Mst_list = [M for (_, _, _, M) in expanded]

    # ---- V span ----
    def mat_to_vec(M):
        return vector(F16, [M[i,j] for i in range(M.nrows()) for j in range(M.ncols())])
    V_vecs = [mat_to_vec(M) for M in Mst_list]
    V_bv = matrix(F16, V_vecs).row_space().basis()
    V_basis = []
    for bv in V_bv:
        MM = matrix(F16, amb, amb)
        for i in range(amb):
            for j in range(amb): MM[i,j] = bv[i*amb + j]
        V_basis.append(MM)

    def rand_span(basis, sz):
        r = zero_matrix(F16, sz, sz)
        for b in basis:
            c = F16.random_element()
            if c != 0: r += c * b
        return r

    def pick_inv(basis, sz, trials=200):
        for _ in range(trials):
            W = rand_span(basis, sz)
            if W.rank() == sz: return W
        W = rand_span(basis, sz) + identity_matrix(F16, sz)
        return W if W.rank() == sz else identity_matrix(F16, sz)

    orb_cap = min(255, order_S)
    def same_orbit(Wa, Wb):
        if Wa.rank() < amb or Wb.rank() < amb: return False
        diff = Wa.inverse() * Wb
        cur = identity_matrix(F16, amb)
        for _ in range(orb_cap):
            if cur == diff: return True
            cur = cur * Sn_full
        return False

    # ---- W1, W2 ----
    tprint("Picking W1,W2 from V ...")
    I_amb = identity_matrix(F16, amb)
    W1 = pick_inv(V_basis, amb)
    if W1.rank() < amb:
        return {"label": label, "status": "W1 not invertible"}

    W2 = None
    for _ in range(150):
        Wc = pick_inv(V_basis, amb)
        if Wc is None: continue
        if not same_orbit(W1, Wc): W2 = Wc; break
    if W2 is None:
        for _ in range(300):
            Wc = rand_span(V_basis, amb) + I_amb
            if Wc.rank() < amb: continue
            if not same_orbit(W1, Wc): W2 = Wc; break
    if W2 is None: W2 = I_amb

    if W2.rank() < amb or same_orbit(W1, W2):
        return {"label": label, "status": "W2 same-orbit failure"}

    # ---- Build polynomial system (full 3*ln vars + lin constraints) ----
    tprint("Building polynomial system...")
    var_names = []
    for ii in range(3):
        for a in range(amb):
            var_names.append('y%d_%d' % (ii+1, a))
    R_poly = PolynomialRing(F16, var_names, order='degrevlex')
    yv = R_poly.gens()
    def Y(i, a): return yv[i*amb + a]

    eqns = []
    for ii in range(3):
        for M in Mst_list:
            p = R_poly(0)
            for a in range(amb):
                for b in range(a, amb):
                    c = M[a,a] if a==b else M[a,b] + M[b,a]
                    if c != 0: p += R_poly(c) * Y(ii,a) * Y(ii,b)
            eqns.append(p)
    for (ii, jj) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
        for M in Mst_list:
            p = R_poly(0)
            for a in range(amb):
                for b in range(amb):
                    c = M[a,b]
                    if c != 0: p += R_poly(c) * Y(ii,a) * Y(jj,b)
            eqns.append(p)

    SnW2 = Sn_full * W2
    for row in range(amb):
        p = R_poly(0)
        for a in range(amb):
            c1, c2, c3 = W1[row,a], W2[row,a], SnW2[row,a]
            if c1 != 0: p += R_poly(c1) * Y(0,a)
            if c2 != 0: p += R_poly(c2) * Y(1,a)
            if c3 != 0: p += R_poly(c3) * Y(2,a)
        eqns.append(p)

    INFILE  = os.path.join(os.getcwd(), "_bench_m4gb.in")
    OUTFILE = INFILE.replace('.in', '.out')

    tprint("System: %d eqns, %d vars" % (len(eqns), tot_vars))

    nsol = 0; dim_gb = -1; sols = []
    m4gb_t = 0; sage_t = 0; total_t = 0

    # ---- Try multiple random pin constraints ----
    # Each pin is a random full linear combination sum c_i * y_i = 1.
    # This hits the solution space with probability ~ 1 - 1/q per try.
    for pin_i in range(MAX_PINS):
        cfs = [F16.random_element() for _ in range(tot_vars)]
        pin_eq = sum(R_poly(cfs[k]) * yv[k] for k in range(tot_vars)) - 1

        all_eqns = eqns + [pin_eq]
        tprint("Pin %d/%d (%d eqns)..." % (pin_i+1, MAX_PINS, len(all_eqns)))

        # -- export --
        with open(INFILE, 'w') as f:
            f.write("$fieldsize %d\n" % q)
            f.write("$vars %s\n" % ' '.join(var_names))
            f.write("# %d eqns %d vars GF(%d)\n" % (len(all_eqns), tot_vars, q))
            for poly in all_eqns:
                terms = []
                for coeff, mono in zip(poly.coefficients(), poly.monomials()):
                    c = gfi(coeff)
                    if c == 0: continue
                    ms = []
                    for vv in mono.variables():
                        e = mono.degree(vv)
                        ms.append(str(vv) if e==1 else "%s^%d" % (str(vv), e))
                    if not ms: terms.append(str(c))
                    elif c == 1: terms.append("*".join(ms))
                    else: terms.append("%d*%s" % (c, "*".join(ms)))
                f.write((" + ".join(terms) if terms else "0") + '\n')

        # -- M4GB --
        tprint("  M4GB (timeout=%ds)..." % M4GB_TIMEOUT)
        t0 = time.time()
        ok_m4gb = False
        if not os.path.isdir(M4GB_HOME):
            return {"label": label, "status": "M4GB dir not found"}
        if not os.path.isfile(os.path.join(M4GB_HOME, "solver.sh")):
            return {"label": label, "status": "solver.sh not found"}

        import subprocess
        try:
            rr = subprocess.run(
                ["bash", os.path.join(M4GB_HOME, "solver.sh"),
                 "-f", str(q), "-n", str(tot_vars), "-v", "1",
                 INFILE, OUTFILE],
                cwd=M4GB_HOME, capture_output=True, text=True,
                timeout=M4GB_TIMEOUT)
            m4gb_t = time.time() - t0
            if rr.returncode == 0:
                ok_m4gb = True
                tprint("  M4GB done %.1fs" % m4gb_t)
            else:
                tprint("  M4GB rc=%d %.1fs" % (rr.returncode, m4gb_t))
        except subprocess.TimeoutExpired:
            m4gb_t = M4GB_TIMEOUT
            tprint("  M4GB TIMEOUT")
        except Exception as e:
            return {"label": label, "status": "M4GB error: %s" % str(e)[:80]}

        if not ok_m4gb:
            continue

        # -- parse --
        gb = []
        if os.path.isfile(OUTFILE):
            with open(OUTFILE, 'r') as f:
                for L in f:
                    L = L.strip()
                    if not L or L.startswith('#'): continue
                    p = R_poly(0)
                    for ts in [t.strip() for t in L.split('+') if t.strip()]:
                        m = re.match(r'^(\d+)\*(.+)', ts)
                        if m:
                            ci = int(m.group(1)); ms = m.group(2)
                        elif ts.isdigit():
                            ci = int(ts); ms = '1'
                        else:
                            ci = 1; ms = ts
                        coeff = int_to_f16(F16, alpha, ci % 16)
                        if coeff != 0: p += coeff * R_poly(ms)
                    if p != 0: gb.append(p)

        if len(gb) == 0:
            continue
        tprint("  GB: %d polynomials" % len(gb))

        # -- Sage solve --
        tprint("  Solving...")
        t1 = time.time()
        try:
            Ig = R_poly.ideal(gb)
            dim_gb = Ig.dimension()
            tprint("  dimGB=%d" % dim_gb)

            if dim_gb == 0:
                sols = list(Ig.variety())
                nsol = len(sols)
            elif 1 <= dim_gb <= 3:
                # Find the actual free variables from the GB:
                # variables that never appear as a leading term.
                all_indices = set(range(tot_vars))
                lead_indices = set()
                for p in gb:
                    if p.is_zero(): continue
                    lt = p.lt()
                    for ei, ev in enumerate(lt.exponents()[0]):
                        if ev > 0: lead_indices.add(ei)
                free_indices = sorted(all_indices - lead_indices)
                if len(free_indices) >= dim_gb:
                    free_indices = free_indices[:dim_gb]
                else:
                    free_indices = list(range(dim_gb))  # fallback
                tprint("  Fixing free vars: %s" % str([var_names[i] for i in free_indices]))

                for fix_i in range(16):
                    extra = [yv[fi] - F16.random_element() for fi in free_indices]
                    try:
                        It = R_poly.ideal(gb + extra)
                        if It.dimension() == 0:
                            new_s = list(It.variety())
                            if len(new_s) > 0:
                                sols = new_s
                                nsol = len(new_s)
                                break
                    except Exception: pass
                if nsol > 0:
                    tprint("  Found %d solutions (dimGB=%d, th~%d)"
                           % (nsol, dim_gb, q**dim_gb))
                else:
                    tprint("  No solutions after 16 fixings")
            else:
                tprint("  dimGB=%d too large, skip" % dim_gb)
        except Exception as e:
            tprint("  Sage error: %s" % str(e)[:80])
            continue

        sage_t = time.time() - t1
        total_t = m4gb_t + sage_t
        tprint("  nsol=%d  Sage=%.1fs" % (nsol, sage_t))

        if nsol > 0:
            break
        tprint("  No solutions, next pin...")

    if nsol == 0:
        return {"label": label, "status": "No solutions found",
                "m4gb_time": m4gb_t, "sage_time": sage_t,
                "total_time": total_t}

    # ---- Verify ----
    verified = False
    if nsol > 0 and len(sols) > 0:
        try:
            s = sols[0]
            y0 = vector(F16, [s[Y(0,a)] for a in range(amb)])
            y1 = vector(F16, [s[Y(1,a)] for a in range(amb)])
            y2 = vector(F16, [s[Y(2,a)] for a in range(amb)])
            yv3 = [y0, y1, y2]
            ok = True; fail_reason = ""
            for ii in range(3):
                for idxM, M in enumerate(Mst_list):
                    if yv3[ii] * M * yv3[ii] != 0:
                        ok = False
                        fail_reason = "Q(y%d) fails on M_%d" % (ii+1, idxM)
            if ok:
                for (ii,jj) in [(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)]:
                    for idxM, M in enumerate(Mst_list):
                        if yv3[ii] * M * yv3[jj] != 0:
                            ok = False
                            fail_reason = "B(y%d,y%d) fails on M_%d" % (ii+1, jj+1, idxM)
            if ok:
                lin_err = W1*y0 + W2*y1 + SnW2*y2
                if not lin_err.is_zero():
                    ok = False
                    fail_reason = "Linear constraint violated"
            verified = ok
            if not ok:
                tprint("Verify FAIL: %s" % fail_reason)
        except Exception as e:
            verified = False
            tprint("Verify exception: %s" % str(e)[:120])
    tprint("Verify: %s" % ("OK" if verified else "FAIL"))
    tprint("Total time for %s: %.1fs" % (label, total_t))

    return {
        "label": label, "v": v, "o": o, "l": l, "q": q,
        "ambient_dim": amb, "tot_vars": tot_vars,
        "tot_eqns": len(eqns) + 1,
        "dim_gb": dim_gb, "nsol": nsol,
        "m4gb_time": m4gb_t, "sage_time": sage_t,
        "total_time": total_t, "verified": verified,
        "status": "OK",
    }

# ============================================================
print("=" * 95)
print("  SNOVA Small-Scale Attack Benchmark")
print("  M4GB: %s   timeout=%ds   pins=%d" % (M4GB_HOME, M4GB_TIMEOUT, MAX_PINS))
print("=" * 95)

bench_start = time.time()

for (v, o, q, l, label) in BENCH_PARAMS:
    print("\n" + "-" * 70)
    print("  %s  [v=%d o=%d q=%d l=%d]" % (label, v, o, q, l))
    print("-" * 70)
    sys.stdout.flush()

    run_results = []
    for run_i in range(NUM_RUNS):
        tprint("--- Run %d/%d ---" % (run_i + 1, NUM_RUNS))
        best = None
        for attempt in range(2):
            seed = 2025 + run_i * 1000 + attempt * 100
            if attempt > 0:
                tprint("  Retry...")
            res = run_one(v, o, q, l, label, seed=seed)
            if res.get("status") == "OK":
                best = res; break
            tprint("  FAILED: %s" % res.get("status"))
        if best is None: best = res
        run_results.append(best)

    # Average OK runs
    ok_runs = [r for r in run_results if r.get("status") == "OK" and r.get("verified")]
    if ok_runs:
        avg_m4gb = sum(r["m4gb_time"] for r in ok_runs) / len(ok_runs)
        avg_sage = sum(r["sage_time"] for r in ok_runs) / len(ok_runs)
        avg_total = sum(r["total_time"] for r in ok_runs) / len(ok_runs)
        tprint("Avg over %d/%d OK runs: M4GB=%.1fs Sage=%.1fs Total=%.1fs" %
               (len(ok_runs), NUM_RUNS, avg_m4gb, avg_sage, avg_total))
        ref = ok_runs[0]
        results.append({
            "label": ref["label"], "v": ref["v"], "o": ref["o"],
            "ambient_dim": ref["ambient_dim"], "tot_vars": ref["tot_vars"],
            "tot_eqns": ref["tot_eqns"],
            "dim_gb": ref["dim_gb"], "nsol": ref["nsol"],
            "m4gb_time": avg_m4gb, "sage_time": avg_sage,
            "total_time": avg_total, "verified": True,
            "status": "OK", "n_runs": len(ok_runs),
        })
    else:
        ref = run_results[0]
        results.append(ref)
        tprint("All %d runs failed: %s" % (NUM_RUNS, ref.get("status", "?")))

# ============================================================
print("\n" + "=" * 95)
print("  RESULTS  (averaged over %d runs per parameter)" % NUM_RUNS)
print("=" * 95)
hdr = "| %-22s | %3s | %3s | %4s | %4s | %5s | %7s | %5s | %8s | %8s | %8s | %7s |" % (
    "Parameters", "v", "o", "ln", "vars", "eqns", "solns", "dim", "M4GB(s)", "Sage(s)", "Total(s)", "Verify")
print(hdr)
sep = "|" + "-"*24 + "|" + "-"*5 + "|" + "-"*5 + "|" + "-"*6 + "|" + "-"*6 + "|" \
      + "-"*7 + "|" + "-"*9 + "|" + "-"*7 + "|" + "-"*10 + "|" + "-"*10 + "|" + "-"*10 + "|" + "-"*9 + "|"
print(sep)
for r in results:
    st = r.get("status", "?")
    if st != "OK":
        print("| %-22s | %3s | %3s | %4s | %4s | %5s | %7s | %5s | %8s | %8s | %8s | %7s |" % (
            r.get("label","?"),
            str(r.get("v","")), str(r.get("o","")),
            str(r.get("ambient_dim","")), str(r.get("tot_vars","")),
            str(r.get("tot_eqns","")),
            "-", "-", "-", "-", "-", st[:6]))
    else:
        print("| %-22s | %3d | %3d | %4d | %4d | %5d | %7d | %5d | %8.1f | %8.1f | %8.1f | %7s |" % (
            r["label"], r["v"], r["o"],
            r["ambient_dim"], r["tot_vars"],
            r["tot_eqns"], r["nsol"], r["dim_gb"],
            r["m4gb_time"], r["sage_time"],
            r["total_time"],
            "OK" if r.get("verified") else "FAIL"))
bench_total = time.time() - bench_start
print("")
print("  Total wall time: %.1f s  (%.1f min)" % (bench_total, bench_total / 60.0))
print("  Sage: %s" % sage.version.version)
print("=" * 95)
