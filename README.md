# Binary Goldbach Exceptional Set in Arithmetic Progressions of Arbitrary Modulus under GRH (Lean 4 Formalization & Paper)

[![Lean 4](https://img.shields.io/badge/Lean-v4.36.0-blue.svg)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.36.0-blueviolet.svg)](https://github.com/leanprover-community/mathlib4)
[![License](https://img.shields.io/badge/License-Apache_2.0-green.svg)](LICENSE)

**Author:** KenRui Lin (Independent Researcher, Guangzhou, China — `longinuslkr@gmail.com`)

This repository contains the complete, zero-`sorry` Lean 4 / Mathlib formalization and the accompanying research manuscript proving a uniform upper bound on the exceptional set in the binary Goldbach problem with both prime summands restricted to arbitrary coprime residue classes modulo any positive integer $r \ge 1$ under the Generalized Riemann Hypothesis (GRH).

---

## Main Theorem

Assuming Dirichlet GRH for all primitive Dirichlet $L$-functions $L(s,\chi)$ (including $\zeta(s)$ at modulus $1$), there exists an absolute effective constant $C > 0$ such that for every integer $X \ge 3$, every positive integer $1 \le r \le X$ (prime or composite, odd or even), and every pair of residue classes $b_1, b_2 \bmod r$ with $\gcd(b_1, r) = \gcd(b_2, r) = 1$, the exceptional set
$$E_r(X; b_1, b_2) := \#\bigl\{1 \le n \le X : 2 \mid n,\; n \equiv b_1 + b_2 \pmod r,\; n \neq p_1 + p_2 \text{ for primes } p_i \equiv b_i \pmod r\bigr\}$$
satisfies
$$E_r(X; b_1, b_2) \le C \min\!\left\{\frac{X}{r},\; \left(\frac{\varphi(r)}{r}\right)^3 \sqrt{X r}\,\log^3(2X)\right\}.$$

In particular, this yields a power-saving exceptional-set bound uniformly for every individual modulus $r \le X^{1/3-\varepsilon}$ and recovers the $O(\sqrt{X}\log^3(2X))$ bound of Goldston at $r = 1$.

In Lean 4, the main theorems are formalized as:

```lean
theorem FareyGoldbach.smoothedTwistEstimate_of_dirichletGRH :
    DirichletGRH → SmoothedTwistEstimate

theorem FareyGoldbach.target_of_dirichletGRH :
    DirichletGRH → Target
```

Both theorems depend **only** on Lean's three standard axioms:
```text
[propext, Classical.choice, Quot.sound]
```
with **zero `sorry`**, **zero `admit`**, and **zero custom axioms** (`DirichletGRH` and `SmoothedTwistEstimate` are ordinary `Prop`-valued definitions passed explicitly as hypotheses).

---

## Repository Contents

- `paper/main.pdf` — Compiled 28-page AMS manuscript.
- `paper/main.tex`, `paper/references.bib` — Complete LaTeX source and BibTeX bibliography.
- `lean/` — Complete Lean 4.36.0 / Mathlib project (`FareyGoldbach`, 13 files, 13,595 lines).
- `notes/` — Early numerical sanity-check script (`verify_step1.py`) and Step 1 exploration notes.

### Lean 4 Module Map (13 files, 13,595 lines)

| Stage / Module | File | Lines | Mathematical Content |
| :--- | :--- | ---: | :--- |
| Root | `lean/FareyGoldbach.lean` | 12 | Package root importing all 12 modules |
| Shared defs | `lean/FareyGoldbach/Defs.lean` | 146 | `Progressions`, `DirichletGRH`, `SmoothedTwistEstimate`, `Target` |
| Stage 2 / A1 | `lean/FareyGoldbach/LocalLogDerivative.lean` | 1,705 | Right-half-plane growth ($\Re s \ge 1/16$), Jensen zero counts, Borel–Carathéodory local $-L'/L$, single-log $\Re s = 1/4$ bound, symmetric good heights |
| Stage 2 / A2 | `lean/FareyGoldbach/QuarticMellin.lean` | 1,525 | Quartic bump $w(x)=16x^2(1-x)^2$ tilted Mellin kernel, second-derivative Van der Corput $O(B^{-1/2})$, full-phase double IBP tail $O((1+|\gamma|)^{-2})$, Mellin inversion |
| Stage 2 / A3 | `lean/FareyGoldbach/SmoothedExplicitFormula.lean` | 1,488 | Elementary $\log/\arctan$ rectangular residue formula, contour shift $\Re s = 2 \to 1/4$, smoothed explicit formula |
| Stage 2 / A4 | `lean/FareyGoldbach/PrimitiveSmoothedTwist.lean` | 770 | Primitive single-log twist bound + unit-interval principal-term discretization (no Euler–Maclaurin) |
| Stage 2 / A5 | `lean/FareyGoldbach/SmoothedTwistOfGRH.lean` | 173 | Reduction from arbitrary $\chi \bmod d$ to primitive $\chi^*$, `smoothedTwistEstimate_of_dirichletGRH`, `target_of_dirichletGRH` |
| Stage 1 / B1 | `lean/FareyGoldbach/CharacterBound.lean` | 791 | Five-line global $H_0$-subgroup character $\ell^1$ bound $\le \sqrt{q/\gcd(r,q)}$ for arbitrary composite $(r,q)$ |
| Stage 1 / B2 | `lean/FareyGoldbach/VoronoiCells.lean` | 451 | Weighted Farey–Voronoi partition of $\mathbb{T}$ with radius sandwich $(2qQ)^{-1} \le \mathrm{rad} \le (qQ)^{-1}$ |
| Stage 1 / C | `lean/FareyGoldbach/SingularSeries.lean` | 1,166 | Unified odd/even finite Euler product ($\ge 1/2$), explicit Rankin tail, discrete quartic convolution lower bound |
| Stage 1 / B3-aux | `lean/FareyGoldbach/PrimeSums.lean` | 2,133 | Elementary $m/\varphi(m) \le 2^{16}m^{1/16}$, prime-sum $L^2$ bound, coprime squarefree inverse-totient estimate |
| Stage 1 / B3 | `lean/FareyGoldbach/ModelAndRemainder.lean` | 2,062 | Uniform $L^\infty$ remainder bound with constant-ratio cutoff $Q_0 = \lfloor Q/2^{24}\rfloor$, model $L^2$ bound, model convolution lower bound |
| Stage 1 / D–E | `lean/FareyGoldbach/DyadicAssembly.lean` | 1,173 | Three-regime dyadic Bessel assembly and global summation (`SmoothedTwistEstimate → Target`) |

*(Note: `lean/FareyGoldbachBlueprint.lean` and `lean/FareyGoldbachCompositeBlueprint.lean` are early historical blueprint drafts and are not imported by `FareyGoldbach`.)*

---

## Reproducing the Lean 4 Verification

Requires [elan](https://github.com/leanprover/elan) (which automatically installs Lean `v4.36.0` from `lean/lean-toolchain`).

```bash
cd lean
lake exe cache get        # optional: download prebuilt Mathlib oleans
lake build FareyGoldbach
```

To independently audit the axiom dependencies of the main theorems:

```bash
cd lean
lake env lean --stdin <<'EOF'
import FareyGoldbach
#print axioms FareyGoldbach.smoothedTwistEstimate_of_dirichletGRH
#print axioms FareyGoldbach.target_of_dirichletGRH
EOF
```

Expected output:
```text
'FareyGoldbach.smoothedTwistEstimate_of_dirichletGRH' depends on axioms: [propext, Classical.choice, Quot.sound]
'FareyGoldbach.target_of_dirichletGRH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Building the Paper PDF

From `paper/`, compile with standard TeX Live (`pdflatex` + `bibtex`) or [Tectonic](https://tectonic-typesetting.github.io/):

```bash
cd paper
pdflatex main && bibtex main && pdflatex main && pdflatex main
# or simply:
tectonic main.tex
```

---

## Transparency & Acknowledgments

The Lean 4 formalization, modular proof-engineering iterations, and manuscript preparation were developed with the assistance of AI tools. Every mathematical claim proved in the formalization is independently machine-checked by the Lean 4 kernel (`v4.36.0` + Mathlib) with zero `sorry` placeholders and no custom axioms.

## Citation

If you use this work, please cite it using `CITATION.cff` or the following BibTeX entry:

```bibtex
@misc{Lin2026GoldbachGRH,
  author = {Lin, KenRui},
  title  = {On the Exceptional Set in the Binary Goldbach Problem in Arithmetic Progressions of Arbitrary Modulus under GRH and Its Formalization in Lean 4},
  year   = {2026},
  note   = {Manuscript and Lean 4 formalization}
}
```

## License

- Lean 4 source code and scripts: [Apache License 2.0](LICENSE) (matching Mathlib).
- Manuscript (`paper/`): Creative Commons Attribution 4.0 International (CC BY 4.0).
