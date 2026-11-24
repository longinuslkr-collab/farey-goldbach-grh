import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient

/-!
# Core Definitions for the Arbitrary-Modulus Farey Goldbach Theorem (under Dirichlet GRH)

This module defines the target theorem `Target`, the single-log smoothed explicit-formula
interface `SmoothedTwistEstimate`, the Dirichlet GRH hypothesis `DirichletGRH`, and the
global `H₀`-subgroup character-sum coefficient `charCoeff`.
-/

open scoped BigOperators

namespace FareyGoldbach

/-- Arbitrary positive integer modulus `r ≥ 1` with two coprime residue classes `b₁, b₂ mod r`.
When `r = 1`, `b₁ = b₂ = 0` (`Nat.Coprime 0 1`), recovering classical binary Goldbach. -/
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

/-- Admissible even integers `1 ≤ n ≤ X` with `n ≡ b₁ + b₂ (mod r)` lacking a representation. -/
noncomputable def exceptions (P : Progressions) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n =>
    Even n ∧ n % P.r = (P.b₁ + P.b₂) % P.r ∧ (primeRepresentations P n).card = 0

noncomputable def dyadicExceptions (P : Progressions) (Y : ℕ) : Finset ℕ :=
  (exceptions P Y).filter fun n => Y / 2 < n

/-- Elementary quartic bump `w(x) = 16 x² (1 - x)²` supported on `(0, 1)`. -/
noncomputable def quarticBump (x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then 16 * x ^ 2 * (1 - x) ^ 2 else 0

noncomputable def primeWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I)

/-- Smoothed prime exponential sum in the progression `r * j + b < Y`. -/
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

/-- Global `H₀`-subgroup character-sum coefficient on `ZMod (r * q)`. -/
noncomputable def charCoeff (r q a b : ℕ) [NeZero (r * q)]
    (χ : DirichletCharacter ℂ (r * q)) : ℂ := by
  classical
  exact ((1 : ℂ) / ((r * q).totient : ℂ)) *
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

end FareyGoldbach
