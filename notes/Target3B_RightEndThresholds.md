# Target 3B: Right-End Balanced Thresholds (`9/19`, Elementary `8/17`, and Spectral `7/15`)

This note archives the independently audited (`ACCEPT`) right-end bounds on the trilinear Kloosterman–Möbius sum arising from the GRH Goldbach long-divisor remainder decomposition $\mathcal{B}(R_Z, R_Z)$.

## 1. Main Theorems (Uniform Over Arbitrary Composite $N$)

For any integer $N \ge 1$, $X = N^x = N^{1-\theta}$, $1 \le J \le H = X^2/N = N^{1-2\theta}$, fixed smooth $\Phi \in C_c^\infty([1,2]^3)$, and any sequence $\beta_b$ with $\|\beta\|_\infty \ll_\varepsilon N^\varepsilon$ for every $\varepsilon > 0$, define
$$S(X, J) := \sum_{\substack{a, b \asymp X \\ (a, b) = 1}} \mu(a)\,\beta_b \sum_{h \asymp J} \Phi\!\left(\frac{a}{X}, \frac{b}{X}, \frac{h}{J}\right) e\!\left(\frac{h N \bar a}{b}\right).$$

1. **Fourth-moment elementary threshold ($\theta > 9/19 \approx 0.473684$)**:
   $$|S(X, J)| \ll_{\Phi, \varepsilon} X^2 N^{-(19\theta - 9)/12 + \varepsilon} \qquad (9/19 < \theta \le 1/2).$$
2. **Flipped sixth-moment elementary threshold ($\theta > 8/17 \approx 0.470588$, zero spectral theory)**:
   $$|S(X, J)| \ll_{\Phi, \varepsilon} X^2 N^{-(17\theta - 8)/10 + \varepsilon} \qquad (8/17 < \theta \le 1/2).$$
3. **Spectral-enhanced threshold ($\theta > 7/15 \approx 0.466667$, using Pascadi, *Forum Math. Pi* 14 (2026), e8, Eq. (5.20) / Cor. 5.5)**:
   $$|S(X, J)| \ll_{\Phi, \varepsilon} X^2 N^{-(15\theta - 7)/10 + \varepsilon} \qquad (7/15 < \theta \le 1/2).$$

All three strictly beat the arbitrary-coefficient Bettin–Chandee Theorem 1 baseline $\theta > 16/33 \approx 0.484848$, hold unconditionally on nonzero frequencies for every composite $N$ (including primorials), and combined with RH on the zero frequency yield strict power savings $T_{U,V}(N) \ll N^{1-\eta}$ on both smooth and sharp dyadic rectangles $U \asymp V \asymp N^\theta$.

## 2. Proof Ingredients & Formalized Core

1. **Double-cutoff Möbius identity** (`FareyGoldbach.Target3BMoebiusSplit`):
   $$\mu = 2\mu_{\le R} - (\mu_{\le R} * \mu_{\le R}) * \mathbf{1} + (\mu_{>R} * \mu_{>R}) * \mathbf{1}.$$
   - Type I ($d \le R^2$, $m \asymp Y = X/d$): Poisson mod $b$ + Ramanujan ($k=0$: $\sum_{b\asymp X}(M,b) \ll X\tau(|M|)$) + full-modulus Weil ($k \ne 0$: $\sum_{k\ne 0}(A,k,b)^{1/2}(1+|k|/K)^{-B_0} \ll K\sum_{e\mid b}e^{-1/2}$).
   - Type II ($a = \ell n$, $\ell, n > R$): swap dyadic boxes so $\ell \asymp L = N^s \in [R, X^{1/2}]$, $n \asymp W = X/L$; 4D smooth Fourier separation on $(\ell/L, n/W, b/X, h/J)$.
2. **Short Type II band ($r \le s \le s_1$)**:
   - Cauchy–Schwarz on $(b, n)$ removes $\beta_b, \gamma_n$ into outer factor $XW N^\varepsilon$; Poisson on $n \bmod b$ gives diagonal $(j-s)/2$, zero-freq $j-x/2$, and nonzero-freq:
     - Elementary Weil bound: $j + s/2 - x/4$.
     - Spectral bound via Pascadi (`arXiv:2404.04239v3`, Eqs. (3.12), (5.18), (5.20)–(5.26), Cor. 15) with $D = \ell_1\ell_2 \asymp L^2$, $C = X\sqrt D$, $m = |N\Delta|$, $X_2(0) = \max(K, D)$ cancelling $\sqrt{D}$ in $\mathcal{T} \le X/\sqrt{mK} \le \sqrt{H/K}$ (and even uncancelled $U_{\rm Bes}$ giving zero excess), $F_{t,\pm}$ Schwartz decay in $t = KW/X$, and quadruple gcd average $\sum (D, N\Delta)^{1/4} \ll J^2 L^2 N^\varepsilon$: lowers nonzero-freq row to $j + 3s/8 - x/4$.
3. **Middle Type II band ($s_1 \le s \le s_2$, flipped 6th moment)** & **Upper Type II band ($s_2 \le s \le x/2$, 4th moment)**:
   - Factor $g = (b, N)$, $b = g q$ with $q \asymp Q = X/g$, $(N/g, q) = 1$.
   - Group $(h, n) \mapsto z \equiv h \bar n \bmod q$ with $\|r_q\|_{6/5} \le \|r_q\|_1^{2/3}\|r_q\|_2^{1/3}$ ($k=3$), or $(h, \ell) \mapsto z \equiv h \bar\ell \bmod q$ with $\|r_q\|_{4/3} \le \|r_q\|_1^{1/2}\|r_q\|_2^{1/2}$ ($k=2$).
   - **Karatsuba–Bourgain–Garaev LCM lemma** (formally proved unconditionally in `FareyGoldbach.Target3BKaratsuba`): any signed rational unit-fraction identity $\sum \sigma_i / f_i = 0$ satisfies $(\operatorname{lcm} f_i)^2 \mid \prod f_i$, yielding $\sum_{q\asymp Q} E_{q,3}(L) \ll (Q L^3 + L^6) N^\varepsilon$ and $\sum_{q\asymp Q} E_{q,2}(W) \ll (Q W^2 + W^4) N^\varepsilon$.
   - Outer Hölder over $q \asymp Q$ produces strictly positive powers of $Q$ in every expanded term ($7/6, 1, 1, 5/6$ for $k=3$; $5/4, 1, 1, 3/4$ for $k=2$), so substituting $Q \le X$ and summing over $g \mid N$ costs only $\tau(N) \ll N^\varepsilon$.
4. **Optimal Cutoffs & Exact Bottlenecks** (`FareyGoldbach.Target3BThresholds`, `notes/check_target3b_thresholds.py`):
   - $r = (x - j_0)/5$, $s_2 = (2x - j_0)/5$; elementary $s_1 = (3x - 2j_0)/10$ gives $(9j_0 - x)/10 < 0 \iff \theta > 8/17$; spectral $s_1 = (6x - 4j_0)/17$ gives $(8j_0 - x)/10 < 0 \iff \theta > 7/15$.
   - Exact obstruction at $j_0 = x/8, s = 3j_0$: both $k=3$ and $k=2$ tight rows hit $0$ while the spectral Cauchy–Schwarz row is $+x/64 > 0$.
5. **Passage to $T_{U,V}(N)$** (smooth or sharp $U \le u < 2U, V \le v < 2V$):
   - Truncate $d_0 = (a,b) \ge N^\kappa$ and boundary strips $au, bv < 2 N^{1-\rho}$ via divisor convolution $O(N^{1-\kappa+\varepsilon} + N^{1-\rho+\varepsilon})$; smooth sharp box over width $\xi = N^{-\sigma}$ at cost $O(N^{1+\varepsilon}(\xi + U^{-1} + V^{-1}))$.
   - Outer Poisson on $u \equiv (N/d_0)\bar a' \pmod{b'}$ truncates nonzero frequencies at $J \ll (B/U) N^\delta$ (absorbing $d_0 > H$ tail cleanly); $\mu(d_0 a') = \mu(d_0)\mu(a')\mathbf{1}_{(a',d_0)=1}$ handled via $\lambda \mid d_0$ inclusion-exclusion in Type I (Poisson at actual scale $Y/\lambda$) and direct factor restriction in Type II; $d_0 = N^w$ improves the margin by $(c-1)w$ ($8w$ for $8/17$, $7w$ for $7/15$); RH bounds the outer zero frequency by $O_\varepsilon(U A^{1/2} N^{O(\rho+\sigma)+\varepsilon})$.
6. **Unbalanced 2D Feasible Region (Elementary 9-row method)**:
   For $p = \min(\alpha, \beta), q = \max(\alpha, \beta)$ with $p + q \le 1$, the elementary 9-row region
   $$(2p+q>1 \wedge 3p+5q>4) \;\lor\; (4p+3q>3 \wedge 8p+11q>9) \;\lor\; (2p+q>1 \wedge 2q-p>1)$$
   strictly contains the Bettin–Chandee region $(19p + 14q > 16 \wedge 8p + 7q > 7)$.

## 3. Lean 4 Verification Scope

- `FareyGoldbach.Target3BMoebiusSplit`: double-cutoff Möbius identity, finite Type I/II split, support vanishing, `9/19` exponent closure & conditional `AnalyticEstimates` power bound.
- `FareyGoldbach.Target3BKaratsuba`: unconditional proof of `karatsuba_lcm_sq_dvd_prod`, `karatsuba_four_reciprocals`, and `karatsuba_six_reciprocals`.
- `FareyGoldbach.Target3BThresholds`: complete rational exponent closures for `8/17`, `7/15`, spectral length/exceptional-factor/normalization checks, shifted Poisson cap (`d_0 = N^w`), and the exact `s = 3j` obstruction.
- Verified with `lake env lean -DwarningAsError=true` and `tests/RouteFAudit.lean` (`[propext, Classical.choice, Quot.sound]` only, zero `sorry`).
