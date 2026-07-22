# SageMath: SNOVA parameter set complexity computation
# Optimized version using formula n = l*v + o 
# Corresponds to Table 5 in the paper.

from sage.all import *
import math

# --------------------------------------------------------------
# 1. Cache and core functions
# --------------------------------------------------------------

comb_cache = {}
def comb(n, k):
    if k < 0 or k > n:
        return 0
    key = (n, k)
    if key not in comb_cache:
        comb_cache[key] = binomial(n, k)
    return comb_cache[key]

coeff_cache = {}
def gen_coefficient_FXL(d, m, n, k_prime):
    key = (d, m, n, k_prime)
    if key in coeff_cache:
        return coeff_cache[key]
    e = n - k_prime + 1
    coeff = 0
    for i in range(min(m, d // 2) + 1):
        exponent = d - 2 * i
        if exponent < 0:
            continue
        sign_i = (-1) ** i
        c1 = comb(m, i)
        c2 = comb(exponent + e - 1, e - 1) if e > 0 else 0
        coeff += sign_i * c1 * c2
    coeff_cache[key] = coeff
    return coeff

degree_cache = {}
def find_degree_FXL(m, n, k_prime, max_iter=1500):
    key = (m, n, k_prime)
    if key in degree_cache:
        return degree_cache[key]
    for d in range(0, max_iter):
        if gen_coefficient_FXL(d, m, n, k_prime) <= 0:
            degree_cache[key] = d
            return d
    degree_cache[key] = max_iter
    return max_iter

complexity_cache = {}
def fxl_complexity_single_kprime(n, m, k_prime, q):
    key = (n, m, k_prime, q)
    if key in complexity_cache:
        return complexity_cache[key]
    try:
        D = find_degree_FXL(m, n, k_prime)
        if D < 0:
            complexity_cache[key] = (float('inf'), None)
            return float('inf'), None
        n_eff = n - k_prime
        term1 = comb(n_eff + D, D)
        term2 = comb(n_eff + 2, 2)
        log_q = log(q, 2).n()
        log_term = 2 * (log_q ** 2) + log_q
        log_c = (k_prime * log_q) + log(3, 2).n() + 2 * log(term1, 2).n() + log(term2, 2).n() + log(log_term, 2).n()
        log_c = float(log_c)
        complexity_cache[key] = (log_c, D)
        return log_c, D
    except:
        complexity_cache[key] = (float('inf'), None)
        return float('inf'), None

def wiedemann_fxl_complexity(n, m, q, k_min=0, k_max=None):
    if k_max is None:
        k_max = n - 1
    min_log = float('inf')
    best_k = None
    best_D = None
    for k_prime in range(k_min, k_max + 1):
        log_c, D = fxl_complexity_single_kprime(n, m, k_prime, q)
        if log_c < min_log:
            min_log = log_c
            best_k = k_prime
            best_D = D
    return min_log, best_k, best_D

def compute_k(v, o):
    return v // o + 1

def C_FXL(a, b, q):
    if a <= 0 or b <= 0:
        return float('inf'), None, None
    return wiedemann_fxl_complexity(n=a, m=b, q=q)

def compute_C1(t, l, v, o, q, m_1):
    log_q = log(q, 2).n()
    if t == 2:
        n = l * v + o
        m = 4 * l ** 2 * m_1 - 2
        log_c, kp, d = C_FXL(n, m, q)
        exp = l * v - 2 * l * o + 1
        total = exp * log_q + log_c
        return float(total), kp, d
    elif t == 3:
        n = 2 * (l * v + o) - (3 * l * o - l * v - 1)
        m = 9 * l ** 2 * m_1 - t * l
        log_c, kp, d = C_FXL(n, m, q)
        return float(log_c), kp, d
    else:
        raise ValueError(f"t={t} invalid for C1")

def compute_C2(t, k, l, v, o, q, m_1):
    log_q = log(q, 2).n()
    if t == 2:
        n = l * v + o
        m = 4 * l ** 2 * m_1 - 2
        log_c, kp, d = C_FXL(n, m, q)
        exp = l * v - 2 * l * o + 1
        total = exp * log_q + log_c
        return float(total), kp, d
    elif 3 <= t <= k - 1:
        n = (t - 1) * (l * v + o)
        m = t ** 2 * l ** 2 * m_1 - t * l
        log_c, kp, d = C_FXL(n, m, q)
        exp = l * v - t * l * o + 1
        total = exp * log_q + log_c
        return float(total), kp, d
    elif t == k:
        n = (k - 1) * (l * v + o) - (k * l * o - l * v - 1)
        m = k ** 2 * l ** 2 * m_1 - t * l
        log_c, kp, d = C_FXL(n, m, q)
        return float(log_c), kp, d
    else:
        raise ValueError(f"t={t} invalid for C2")

def total_complexity(t, k, l, v, o, q, m_1):
    if k == 3:
        return compute_C1(t, l, v, o, q, m_1)
    elif k >= 4:
        return compute_C2(t, k, l, v, o, q, m_1)
    else:
        raise ValueError(f"k={k} invalid")

def find_optimal_t(l, v, o, q, m_1):
    k = compute_k(v, o)
    if k < 3:
        raise ValueError("k must >=3")
    min_log = float('inf')
    best_t = None
    best_kp = None
    best_D = None
    for t in range(2, k + 1):
        c_log, kp, d = total_complexity(t, k, l, v, o, q, m_1)
        if c_log < min_log:
            min_log = c_log
            best_t = t
            best_kp = kp
            best_D = d
    return best_t, min_log, k, best_kp, best_D

# --------------------------------------------------------------
# 2. Parameter sets
# --------------------------------------------------------------

# Second-Round SNOVA parameters (Table 6)
table6_params = [
    {"SL": "I",  "v":37, "o":17, "q":16, "l":2, "m1":17},
    {"SL": "I",  "v":25, "o":8,  "q":16, "l":3, "m1":8},
    {"SL": "I",  "v":24, "o":5,  "q":16, "l":4, "m1":5},
    {"SL": "II", "v":56, "o":25, "q":16, "l":2, "m1":25},
    {"SL": "II", "v":49, "o":11, "q":16, "l":3, "m1":11},
    {"SL": "II", "v":37, "o":8,  "q":16, "l":4, "m1":8},
    {"SL": "II", "v":24, "o":5,  "q":16, "l":5, "m1":5},
    {"SL": "V",  "v":75, "o":33, "q":16, "l":2, "m1":33},
    {"SL": "V",  "v":66, "o":15, "q":16, "l":3, "m1":15},
    {"SL": "V",  "v":60, "o":10, "q":16, "l":4, "m1":10},
    {"SL": "V",  "v":29, "o":6,  "q":16, "l":5, "m1":6},
]

# Reformulated SNOVA parameters (Table 7)
table7_params = [
    {"SL": "I",   "v":43, "o":6,  "q":16, "l":2, "r":6,  "m1":16, "m2":72},
    {"SL": "I",   "v":44, "o":5,  "q":16, "l":2, "r":8,  "m1":16, "m2":80},
    {"SL": "I",   "v":36, "o":5,  "q":16, "l":3, "r":5,  "m1":9,  "m2":75},
    {"SL": "I",   "v":24, "o":3,  "q":16, "l":4, "r":7,  "m1":6,  "m2":84},
    {"SL": "I",   "v":28, "o":4,  "q":16, "l":4, "r":5,  "m1":5,  "m2":80},
    {"SL": "III", "v":52, "o":8,  "q":16, "l":2, "r":7,  "m1":24, "m2":112},
    {"SL": "III", "v":48, "o":8,  "q":16, "l":3, "r":4,  "m1":11, "m2":96},
    {"SL": "III", "v":38, "o":5,  "q":16, "l":4, "r":5,  "m1":7,  "m2":100},
    {"SL": "III", "v":44, "o":6,  "q":16, "l":4, "r":5,  "m1":8,  "m2":120},
    {"SL": "V",   "v":86, "o":11, "q":16, "l":2, "r":6,  "m1":32, "m2":132},
    {"SL": "V",   "v":64, "o":9,  "q":16, "l":3, "r":5,  "m1":15, "m2":135},
    {"SL": "V",   "v":52, "o":6,  "q":16, "l":4, "r":6,  "m1":9,  "m2":144},
    {"SL": "V",   "v":52, "o":7,  "q":16, "l":4, "r":5,  "m1":9,  "m2":140},
    {"SL": "V",   "v":56, "o":8,  "q":16, "l":4, "r":5,  "m1":10, "m2":160},
]

# --------------------------------------------------------------
# 3. Compute and output summary table
# --------------------------------------------------------------

def compute_row(source, params):
    v = params['v']
    o = params['o']
    q = params['q']
    l = params['l']
    m1 = params['m1']
    t_opt, log_c, k, kp, D = find_optimal_t(l, v, o, q, m1)
    if source == "Second-Round":
        param_str = f"({v},{o},{q},{l})"
    else:
        r = params['r']; m2 = params['m2']
        param_str = f"({v},{o},{q},{l},{r},{m1},{m2})"
    return {
        "source": source,
        "SL": params['SL'],
        "params": param_str,
        "log2": log_c,
        "t": t_opt,
        "kp": kp,
        "D": D
    }

all_rows = []
for p in table6_params:
    all_rows.append(compute_row("Second-Round", p))
for p in table7_params:
    all_rows.append(compute_row("Reformulated", p))

rows_sorted = sorted(all_rows, key=lambda x: (x['source'], x['SL']))

print("\n## SNOVA: Optimal Complexity per Parameter Set (n = l*v + o)\n")
print("| Source         | SL  | Parameters              | log2(complexity) | optimal t | k' | D |")
print("|----------------|-----|-------------------------|------------------|-----------|---|----|")
for row in rows_sorted:
    log_str = f"{row['log2']:.2f}" if row['log2'] != float('inf') else "inf"
    print(f"| {row['source']:14s} | {row['SL']:3s} | {row['params']:23s} | {log_str:16s} | {str(row['t']):9s} | {str(row['kp']):2s} | {str(row['D']):2s} |")
