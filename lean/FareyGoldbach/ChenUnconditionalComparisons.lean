import FareyGoldbach.ChenRosserProfiles
import FareyGoldbach.RosserBasePoints

/-! # Unconditional Rosser comparisons for Chen's sequence -/

open Filter
open scoped Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace FareyGoldbach

theorem chenFloorRosserProfiles_unconditional {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2) :
    ChenFloorRosserProfiles θ := by
  apply chenFloorRosserProfiles_of_uniform hθ hθ₂
  obtain ⟨K,hK,hlocal⟩ := chenBoundingSieve_dimension_one
  obtain ⟨C,hC,hD⟩ := rosser_first_interval_uniform K hK
  refine ⟨C,hC,?_⟩
  filter_upwards [hD] with D hD
  intro N w he _ hw
  let S := chenBoundingSieve he w
  have hs : HasDimensionOneLocalProductBound S K := hlocal N w he
  have hcut (p : ℕ) (hp : p ∈ S.prodPrimes.primeFactors) :
      p < ⌈(D:ℝ)^(1/chenSieveParameter D w)⌉₊ := by
    rw [← hw]
    apply chenSiftingPrime_lt_cutoff (N:=N)
    simpa only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors] using hp
  have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S = chenDensityProduct N w := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors chenDensityProduct
    simp only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors,chenBoundingSieve_nu,
      chenDivisorDensity]
  have hν : (S.nu : ℕ→ℝ) = chenDivisorDensity := rfl
  simpa only [hV,hν,S,chenBoundingSieve_prodPrimes] using
    hD S (chenSieveParameter D w) hs hcut

theorem chenRosserMainComparisons_unconditional {θ : ℝ} (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2) :
    ∃ U : ℕ→ℝ, (∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N) ∧
      ChenRosserMainComparisons θ U :=
  ⟨chenCanonicalU, eventually_inf_principal.mp chenCanonicalU_eventually_ge_half,
    chenRosserMainComparisons_of_floorProfiles hθ₁ hθ₂
      (chenFloorRosserProfiles_unconditional hθ₁ hθ₂)⟩

theorem chen_count_lower_of_distributions
    (hA : ChenPrimeAPDistribution) (hB : ChenSwitchingDistribution) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) :=
  chen_count_lower_of_distributions_and_comparisons hA hB
    (fun _ => chenRosserMainComparisons_unconditional)

theorem chen_theorem_of_distributions
    (hA : ChenPrimeAPDistribution) (hB : ChenSwitchingDistribution) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N :=
  chen_theorem_of_distributions_and_comparisons hA hB
    (fun _ => chenRosserMainComparisons_unconditional)

end FareyGoldbach
