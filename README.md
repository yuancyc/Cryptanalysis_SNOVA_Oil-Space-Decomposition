# Cryptanalysis_SNOVA_Oil-Space-Decomposition

Experimental code accompanying the paper **"New Key Recovery Attacks on SNOVA with the Oil Space Decomposition."**

## Environment

| Component | Specification |
|-----------|---------------|
| Platform  | VMware Virtual Machine (Linux) |
| Memory    | 12 GB |
| CPU       | 2 processors × 4 cores |
| Disk      | 80 GB |
| Software  | SageMath 10.8 |

## File Overview

### Complexity Computation (Paper Tables 3 & 5)

| File | Paper Reference | Description |
|------|----------------|-------------|
| `Basic Complexity.sage` | Table 3 | Optimal attack complexity with corrected formula `n = l*(v+o)` |
| `Optimized Complexity.sage` | Table 5 | Optimal attack complexity with original formula `n = l*v + o` |

```python
sage "Basic Complexity.sage"
```

Outputs a Markdown table with `log2(complexity)`, optimal `t`, `k'`, and `D` for each SNOVA parameter set.

### Independence Verification

| File | Description |
|------|-------------|
| `snova_toy_independence.sage` | Verifies the number of quadratically independent equations in System (4) after eliminating `y0`. Across all tested parameter sets, the script consistently reports a deficit of exactly `t·l` equations. |

The statement in Section 4.1 ("Attack Description") — *"In contrast to [4], distinct variables reduce redundant equations"* — is indeed correct: we cannot mimic the approach of [4] to prove the existence of redundant equations of the kind found there. Nevertheless, our experiments consistently confirm a deficit of exactly `t·l` equations. While we are unable to provide a rigorous derivation of the specific algebraic redundancy relations, this has negligible impact on the attack complexity. The updated complexity figures are given at the end of this document.

### Full Attack Implementation

These scripts implement the full attack without assuming knowledge of the oil subspace. They construct System (4) and solve it using the M4GB Groebner-basis solver. **Ensure `m4gb/` is in the same directory as these scripts.** The attack was benchmarked across 5 small parameter sets.

| File | Parameters | Variables | Equations |
|------|------------|-----------|------------|
| `snova_toy_(2,1,16,2).sage` | `SNOVA(2,1,16,2)` | 18 | 43 |
| `snova_toy_(2,1,16,3).sage` | `SNOVA(2,1,16,3)` | 27 | 91 |
| `snova_benchmark.sage` | All 5 sets below | — | — |

```python
sage snova_benchmark.sage
```

Benchmarked parameters:

| `SNOVA(v,o,q,l)` | `l*n` | Variables | Equations |
|------------------|-------|-----------|------------|
| `(2,1,16,2)` | 6 | 18 | 43 |
| `(2,1,16,3)` | 9 | 27 | 91 |
| `(2,1,16,4)` | 12 | 36 | 157 |
| `(4,2,16,2)` | 12 | 36 | 85 |
| `(5,2,16,2)` | 14 | 42 | 86 |

**Benchmark results** (averaged over 5 runs per parameter set):

| Parameters             | v | o | l·n | vars | eqns | solns | dim | M4GB(s) | Sage(s) | Total(s) | Verify |
|------------------------|---|---|-----|------|------|-------|-----|---------|---------|----------|--------|
| SNOVA(2,1,16,2)        | 2 | 1 | 6   | 18   | 43   | 2     | 1   | 0.2     | 4.1     | 4.3      | OK     |
| SNOVA(2,1,16,3)        | 2 | 1 | 9   | 27   | 91   | 1     | 2   | 0.2     | 0.3     | 0.5      | OK     |
| SNOVA(2,1,16,4)        | 2 | 1 | 12  | 36   | 157  | 1     | 3   | 0.5     | 0.3     | 0.8      | OK     |
| SNOVA(4,2,16,2)        | 4 | 2 | 12  | 36   | 85   | 1     | 3   | 11.9    | 0.3     | 12.3     | OK     |

> Total wall time: 109.4 s (1.8 min). Sage: 10.8 s.

Due to our environment configuration limitations, we assume the oil subspace is known for fast verification.

### O-Known Fast Verification

These scripts assume the oil subspace `O` is known and use nullspace enumeration to rapidly verify the correctness of the paper's derivation.

| File | Parameters |
|------|------------|
| `snova_toy_know_(2,1,16,4).sage` | `SNOVA(2,1,16,4)` |
| `snova_toy_know_(2,1,16,5).sage` | `SNOVA(2,1,16,5)` |
| `snova_toy_know_(5,2,16,2).sage` | `SNOVA(5,2,16,2)` |
| `snova_toy_know_(5,2,16,3).sage` | `SNOVA(5,2,16,3)` |
| `snova_toy_know_(5,2,16,4).sage` | `SNOVA(5,2,16,4)` |
| `snova_toy_know_(10,4,16,3).sage` | `SNOVA(10,4,16,3)` |

## Usage

Run any script with SageMath:

```bash
sage "Basic Complexity.sage"
sage "snova_toy_(2,1,16,2).sage"
sage snova_benchmark.sage
# ... (see file overview above for all scripts)
```

### M4GB Path Configuration

Please follow the instructions in the m4gb project to install m4gb. Scripts that invoke M4GB (`snova_toy_(2,1,16,2).sage`, `snova_toy_(2,1,16,3).sage`, `snova_benchmark.sage`) use `./m4gb` relative to the working directory by default. To use a different path, edit the `M4GB_HOME` line near the top of each script:

```python
M4GB_HOME = os.path.join(os.getcwd(), "m4gb")
```

## Notes

- The `m4gb/` directory contains the M4GB solver (`m4gb-master/`) and the OpenF4 library (`openf4-master/`). Both must be compiled before use.
- All scripts use a fixed random seed (`2025`) for reproducibility.
- Scripts with `know` in the filename assume the oil subspace is given for fast verification; those without implement the full black-box attack.

## Basic Complexity Results (`n = l*(v+o)`)

Output of `Basic Complexity.sage` (Corresponding Table 3).

| Source         | SL  | Parameters              | log₂(complexity) | optimal t | k' | D |
|----------------|-----|-------------------------|------------------|-----------|---|----|
| Reformulated   | I   | (43,6,16,2,6,16,72)     | 289.53           | 8         | 0  | 21 |
| Reformulated   | I   | (44,5,16,2,8,16,80)     | 309.02           | 9         | 0  | 22 |
| Reformulated   | I   | (36,5,16,3,5,9,75)      | 355.67           | 8         | 0  | 26 |
| Reformulated   | I   | (24,3,16,4,7,6,84)      | 268.76           | 8         | 0  | 18 |
| Reformulated   | I   | (28,4,16,4,5,5,80)      | 371.31           | 7         | 0  | 28 |
| Reformulated   | III | (52,8,16,2,7,24,112)    | 292.77           | 7         | 0  | 21 |
| Reformulated   | III | (48,8,16,3,4,11,96)     | 454.68           | 6         | 0  | 36 |
| Reformulated   | III | (38,5,16,4,5,7,100)     | 477.63           | 8         | 0  | 35 |
| Reformulated   | III | (44,6,16,4,5,8,120)     | 544.86           | 8         | 0  | 40 |
| Reformulated   | V   | (86,11,16,2,6,32,132)   | 521.74           | 8         | 0  | 38 |
| Reformulated   | V   | (64,9,16,3,5,15,135)    | 594.70           | 7         | 0  | 44 |
| Reformulated   | V   | (52,6,16,4,6,9,144)     | 665.23           | 9         | 0  | 48 |
| Reformulated   | V   | (52,7,16,4,5,9,140)     | 648.24           | 8         | 0  | 48 |
| Reformulated   | V   | (56,8,16,4,5,10,160)    | 663.38           | 7         | 0  | 50 |
| Second-Round   | I   | (37,17,16,2)            | 153.76           | 2         | 0  | 12 |
| Second-Round   | I   | (25,8,16,3)             | 179.46           | 3         | 0  | 14 |
| Second-Round   | I   | (24,5,16,4)             | 265.59           | 5         | 0  | 21 |
| Second-Round   | II  | (56,25,16,2)            | 221.18           | 2         | 0  | 16 |
| Second-Round   | II  | (49,11,16,3)            | 440.75           | 5         | 0  | 37 |
| Second-Round   | II  | (37,8,16,4)             | 370.08           | 5         | 0  | 29 |
| Second-Round   | II  | (24,5,16,5)             | 279.44           | 5         | 0  | 21 |
| Second-Round   | V   | (75,33,16,2)            | 288.05           | 2         | 0  | 20 |
| Second-Round   | V   | (66,15,16,3)            | 563.44           | 5         | 0  | 47 |
| Second-Round   | V   | (60,10,16,4)            | 725.79           | 6         | 0  | 58 |
| Second-Round   | V   | (29,6,16,5)             | 321.06           | 5         | 0  | 24 |

## Optimized Complexity Results (`n = l*v + o`)

Output of `Optimized Complexity.sage` (Corresponding Table 5).

| Source         | SL  | Parameters              | log₂(complexity) | optimal t | k' | D |
|----------------|-----|-------------------------|------------------|-----------|---|----|
| Reformulated   | I   | (43,6,16,2,6,16,72)     | 265.53           | 8         | 0  | 19 |
| Reformulated   | I   | (44,5,16,2,8,16,80)     | 284.98           | 9         | 0  | 20 |
| Reformulated   | I   | (36,5,16,3,5,9,75)      | 308.77           | 8         | 0  | 22 |
| Reformulated   | I   | (24,3,16,4,7,6,84)      | 242.67           | 8         | 0  | 16 |
| Reformulated   | I   | (28,4,16,4,5,5,80)      | 315.25           | 7         | 0  | 23 |
| Reformulated   | III | (52,8,16,2,7,24,112)    | 261.73           | 7         | 1  | 18 |
| Reformulated   | III | (48,8,16,3,4,11,96)     | 389.42           | 6         | 0  | 30 |
| Reformulated   | III | (38,5,16,4,5,7,100)     | 414.70           | 8         | 2  | 29 |
| Reformulated   | III | (44,6,16,4,5,8,120)     | 472.38           | 8         | 0  | 34 |
| Reformulated   | V   | (86,11,16,2,6,32,132)   | 473.88           | 8         | 0  | 34 |
| Reformulated   | V   | (64,9,16,3,5,15,135)    | 524.09           | 8         | 0  | 38 |
| Reformulated   | V   | (52,6,16,4,6,9,144)     | 590.71           | 9         | 0  | 42 |
| Reformulated   | V   | (52,7,16,4,5,9,140)     | 563.83           | 8         | 0  | 41 |
| Reformulated   | V   | (56,8,16,4,5,10,160)    | 569.89           | 7         | 0  | 42 |
| Second-Round   | I   | (37,17,16,2)            | 123.28           | 3         | 0  | 10 |
| Second-Round   | I   | (25,8,16,3)             | 144.23           | 4         | 0  | 11 |
| Second-Round   | I   | (24,5,16,4)             | 221.48           | 5         | 0  | 17 |
| Second-Round   | II  | (56,25,16,2)            | 171.00           | 3         | 0  | 14 |
| Second-Round   | II  | (49,11,16,3)            | 358.03           | 5         | 0  | 29 |
| Second-Round   | II  | (37,8,16,4)             | 302.61           | 5         | 0  | 23 |
| Second-Round   | II  | (24,5,16,5)             | 222.49           | 5         | 0  | 16 |
| Second-Round   | V   | (75,33,16,2)            | 218.33           | 3         | 0  | 18 |
| Second-Round   | V   | (66,15,16,3)            | 456.67           | 5         | 2  | 36 |
| Second-Round   | V   | (60,10,16,4)            | 599.54           | 6         | 1  | 46 |
| Second-Round   | V   | (29,6,16,5)             | 262.31           | 5         | 0  | 19 |

