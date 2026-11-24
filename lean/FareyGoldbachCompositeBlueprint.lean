import Mathlib

/-!
# Arbitrary-Modulus Binary Goldbach Exceptional Set under Dirichlet GRH (v2 Blueprint)

Upgraded from `FareyGoldbachBlueprint.lean` (v1, odd prime `r`, sharp cutoff, `log^5`)
using our Step 1 mathematical improvements:

1. **Arbitrary positive integer modulus `r ≥ 1`** (odd, even, prime, or composite),
   via the 5-line global subgroup `H₀ = {1 + m * lcm(r, q) mod (r*q)}` of order `g = gcd(r, q)`.
   No prime factorization or case split between `(q, r) = 1` and `r ∣ q` is needed for the
   `ℓ¹` character bound `∑ |c_χ| ≤ √(φ(rq) / (g * φ(r))) ≤ √(q / g)`.
2. **Quartic polynomial smoothing `w(x) = 16 x² (1 - x)²`** on `(0, 1)`:
   - Shaves **two** log powers (`log^5 → log^3`), matching Goldston's `√X log³ X` at `r = 1`.
   - Eliminates `Z_b` vs. `Y` boundary mismatch (`w((r*j + b) / Y) = 0` for `r*j + b ≥ Y`).
   - Makes Module A (`DirichletGRH → SmoothedTwistEstimate`) dramatically cleaner:
     double Stieltjes integration by parts passes to the absolutely convergent explicit
     formula for `ψ₁(u, χ)` (no Perron truncation height `T`, no prime-power jump error,
     and the `s = 0` constant term `c₀(χ) * u` annihilates identically since `u'' = 0`).
3. **Composite density bonus `(φ(r) / r)³`**:
   Using `∑_{q ≤ Q₀, (q,r)=1} μ²(q)/φ(q) ≪ (φ(r)/r) log(2Q₀)` and the dyadic branch
   split at `r ≤ Y^(2/5)` vs. `r > Y^(2/5)`.

## Module Dependency Tree

```text
DirichletGRH
  → A1 (unitIntervalZeroCount + ψ₁ absolutely convergent explicit formula)
  → A2 (SmoothedTwistEstimate : single-log √(Y(1+|t|Y)) log(2dY))
      → B0 (primePowerMass + q=1 smoothed L¹ weight)
B0 + A2 + B1 (global H₀ character expansion) + B2 (weighted Voronoi cells)
  → B3 (remainder_sup ≪ Y^(3/4) r^(-1/4) L  &  L² norms ≪ (r/φ(r)) H L)
B2 + C1 (Ramanujan sum) + C2 (finite Euler product, odd & even r) + C2b (quartic convolution ≥ c₀ H)
  → C3 (model Fourier coeff lower bound ≥ c (r/φ(r))² H)
B3 + C3 + D1 (AddCircle Fourier convolution & Bessel)
  → D2 (DyadicBound, split at r ≤ Y^(2/5) vs r > Y^(2/5))
D2 + dyadic geometric sum + trivial congruence count
  → E (Global Target)
```

## Build Order Recommendation (Two-Stage Lean 4 Plan)
- **Stage 1 (Fast, pure Mathlib — ZERO `sorry`):** Implement Modules `B`, `C`, `D`, `E`
  proving `target_of_smoothedTwistEstimate : SmoothedTwistEstimate → Target`.
  Every ingredient (`ZMod.unitsMap_surjective`, `DirichletCharacter.sum_char_inv_mul_char_eq`,
  `Real.exists_rat_abs_sub_le_and_den_le`, `AddCircle.hasSum_sq_fourierCoeff`) is already
  in Mathlib!
- **Stage 2 (Analytic Core):** Prove `smoothedTwistEstimate_of_grh : DirichletGRH → SmoothedTwistEstimate`
  (Module `A`), reusing `PrimeNumberTheoremAnd` / Mathlib `DirichletCharacter.LFunction`
  contour-integration infrastructure.
-/

open scoped BigOperators

namespace FareyGoldbachComposite

/-- Arbitrary positive integer modulus `r ≥ 1` with two coprime residue classes `b₁, b₂ mod r`.
Note: `r = 1` gives `b₁ = b₂ = 0` (`Nat.Coprime 0 1`), recovering classical binary Goldbach! -/
structure Progressions where
  r : ℕ
  r_pos : 0 < r
  b₁ : ℕ
  b₂ : ℕ
  b₁_lt : b₁ < r
  b₂_lt : b₂ < r
  coprime₁ : Nat.Coprime b₁ r
  coprime₂ : Nat.Coprime b₂ r

/-- Ordered representations `n = p₁ + p₂` with primes `pᵢ ≡ bᵢ (mod r)`. -/
noncomputable def primeRepresentations (P : Progressions) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 2 n).product (Finset.Icc 2 n)).filter fun pq =>
    pq.1.Prime ∧ pq.2.Prime ∧ pq.1 + pq.2 = n ∧
      pq.1 % P.r = P.b₁ ∧ pq.2 % P.r = P.b₂

/-- Admissible even integers `1 ≤ n ≤ X` with `n ≡ b₁ + b₂ (mod r)` lacking a representation.
When `2 ∣ r`, `Even n` is automatically implied by `n % r = (b₁ + b₂) % r`. -/
noncomputable def exceptions (P : Progressions) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n =>
    Even n ∧ n % P.r = (P.b₁ + P.b₂) % P.r ∧ (primeRepresentations P n).card = 0

noncomputable def dyadicExceptions (P : Progressions) (Y : ℕ) : Finset ℕ :=
  (exceptions P Y).filter fun n => Y / 2 < n

/-- Elementary quartic bump `w(x) = 16 x² (1 - x)²` supported on `(0, 1)`.
Satisfies `0 ≤ w(x) ≤ 1`, `w ∈ C¹(ℝ)`, `w(0) = w'(0) = w(1) = w'(1) = 0`, and `w'' ∈ L^∞`. -/
noncomputable def quarticBump (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then 16 * x ^ 2 * (1 - x) ^ 2 else 0

noncomputable def primeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)

/-- Smoothed prime exponential sum in the progression `r * j + b < Y`.
Because `quarticBump` vanishes for `r * j + b ≥ Y`, there is no cutoff mismatch at `Y`. -/
noncomputable def smoothedPrimeSum (r b Y : ℕ) (α : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Y / r + 1),
    ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) *
      e (α * (j : ℝ))

/-- Smoothed model kernel `V_b^{(w)}(β)` on the progression `r * j + b < Y`. -/
noncomputable def smoothedKernel (r b Y : ℕ) (β : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Y / r + 1),
    (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ))

noncomputable def ramanujanSum (q n : ℕ) : ℂ :=
  ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
    e ((a : ℝ) * (n : ℝ) / (q : ℝ))

noncomputable def singularTrunc (r n cutoff : ℕ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 cutoff).filter (fun q => Nat.Coprime q r),
    (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n /
      (q.totient : ℂ) ^ 2

/-- Dirichlet GRH for all primitive Dirichlet characters (including `d = 1`, i.e., `ζ(s)`). -/
def DirichletGRH : Prop :=
  ∀ (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

/-- Smoothed twisted remainder for `χ mod d` with the quartic bump weight. -/
noncomputable def smoothedTiltedRemainder {d : ℕ} (χ : DirichletCharacter ℂ d)
    (Y : ℕ) (t : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 Y,
    (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod d) -
      (if χ = 1 then (1 : ℂ) else 0)) *
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * e (t * (n : ℝ))

/-- Single-log smoothed twisted explicit-formula bound (Module A output, Module B–E input). -/
def SmoothedTwistEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) *
            Real.log (2 * (d : ℝ) * Y)

/-- Upgraded dyadic exception budget: `(φ(r)/r)³ * √(Y r) * log³(2Y)`. -/
noncomputable def dyadicBudget (Y r : ℕ) : ℝ :=
  ((r.totient : ℝ) / (r : ℝ)) ^ 3 *
    Real.sqrt ((Y : ℝ) * r) * (Real.log (2 * (Y : ℝ))) ^ 3

def DyadicBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) (Y : ℕ), P.r ≤ Y →
    ((dyadicExceptions P Y).card : ℝ) ≤ C * dyadicBudget Y P.r

/-- Main theorem target: holds for ALL positive integer moduli `r ≤ X`. -/
def Target : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (P : Progressions) (X : ℕ), 3 ≤ X → P.r ≤ X →
    ((exceptions P X).card : ℝ) ≤
      C * min ((X : ℝ) / P.r) (dyadicBudget X P.r)

/-- Global `H₀`-subgroup character-sum coefficient on `ZMod (r * q)`.
Module B1 proves:
1. If `1 < Nat.gcd r q`, then `charCoeff r q a b 1 = 0`.
2. `∑ χ, ‖charCoeff r q a b χ‖ ≤ √((r * q).totient / (Nat.gcd r q * r.totient)) ≤ √(q / Nat.gcd r q)`. -/
noncomputable def charCoeff (r q : ℕ) (a b : ℕ) [NeZero (r * q)]
    (χ : DirichletCharacter ℂ (r * q)) : ℂ :=
  ((1 : ℂ) / ((r * q).totient : ℂ)) *
    ∑ u ∈ (Finset.univ : Finset (ZMod (r * q))).filter
        (fun u => IsUnit u ∧ u.val % r = b % r),
      e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) * star (χ u)

/-- Basic counting bridge from Bessel energy to exceptional-set cardinality. -/
theorem card_mul_sq_le_sum {ι : Type*} {bad allTargets : Finset ι}
    (hsub : bad ⊆ allTargets) (err : ι → ℂ) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) (hbad : ∀ i ∈ bad, threshold ≤ ‖err i‖) :
    (bad.card : ℝ) * threshold ^ 2 ≤ ∑ i ∈ allTargets, ‖err i‖ ^ 2 := by
  classical
  calc
    (bad.card : ℝ) * threshold ^ 2 = ∑ _i ∈ bad, threshold ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ bad, ‖err i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hp := mul_nonneg (sub_nonneg.mpr (hbad i hi))
        (add_nonneg (norm_nonneg (err i)) hthreshold)
      nlinarith
    _ ≤ ∑ i ∈ allTargets, ‖err i‖ ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
        intro i _ _
        exact sq_nonneg ‖err i‖)

end FareyGoldbachComposite
