import FareyGoldbach.RosserSuzukiCoefficients
import FareyGoldbach.LinearSieveFactors
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147JurkatRichertInterval
import FareyGoldbach.RosserSuzukiUpperInterval
import FareyGoldbach.RosserUniformEnvelope
import FareyGoldbach.RosserClosedUpper

/-! # The sharp upper and lower base points of the one-dimensional Rosser sieve

The estimates use the concrete Section 13 solution and the all-depth discrete
comparison. The coefficient on the left is the integer-indexed polynomial of
this project. The errors O_K((log D)^(-1/2)) are uniform in the sieve carrier.
-/

open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open Filter
open scoped Topology
open MathlibNt.SieveTheory MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace FareyGoldbach

private theorem basePoint_products_nonneg (S : BoundingSieve) :
    0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  apply Finset.prod_nonneg
  intro p hp
  exact sub_nonneg.mpr (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp)
    ((Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp).2).le

private theorem basePoint_cutoff_bounds {D : ℕ} (hD : 2 ≤ D) {s : ℝ} (hs : 1 ≤ s) :
    2 ≤ ⌈(D:ℝ)^(1/s)⌉₊ ∧ ⌈(D:ℝ)^(1/s)⌉₊ ≤ D := by
  have hDr : (1:ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hr : (1:ℝ) < (D:ℝ)^(1/s) := Real.one_lt_rpow hDr (by positivity)
  refine ⟨?_,Nat.ceil_le.mpr (Real.rpow_le_self_of_one_le hDr.le
    ((div_le_one (by positivity)).mpr hs))⟩
  have hceil := hr.trans_le (Nat.le_ceil _)
  exact_mod_cast hceil

private theorem basePoint_large_geometry :
    ∀ᶠ D : ℕ in atTop, 2 ≤ D ∧ 4 ≤ sourceSigma (D : ℝ) 16 ∧
      (4 : ℝ)^(16:ℝ) ≤ Real.log (D : ℝ) := by
  obtain ⟨D₀,_,hσ⟩ := exists_sourceSigma_fixed_lower_threshold 16 4 (by norm_num)
  have hc : Tendsto (fun D : ℕ => (D : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hc.eventually_ge_atTop D₀,
    (Real.tendsto_log_atTop.comp hc).eventually_ge_atTop ((4:ℝ)^(16:ℝ))] with D hd hD hlog
  exact ⟨hd,hσ _ hD,hlog⟩

private theorem basePoint_lower_carrier (S : BoundingSieve) (D z : ℕ)
    (hc : ∀ p ∈ S.prodPrimes.primeFactors, p < z) :
    S.mainSum (LinearSieve.lowerRosserWeight S.prodPrimes D) =
        LinearSieve.lowerRosserSetDensitySum S.nu D (suzukiSupportedBelow S z) ∧
      suzukiVProduct S (z:ℝ) = AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  constructor
  · rw [suzukiSupportedBelow, Finset.filter_eq_self.mpr hc]
    exact LinearSieve.mainSum_lowerRosserWeight_eq_setDensitySum S D
  · unfold suzukiVProduct AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    rw [Finset.filter_eq_self.mpr (fun p hp => Nat.cast_lt.mpr (hc p hp))]

private theorem basePoint_source_parameters : SuzukiClaim145SourceParameters 16 (1/2) 7 := by
  constructor <;> norm_num

private theorem rosser_suzuki_upper_first {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {s : ℝ} (hs1 : 1<s) (hs3 : s≤3) :
    suzukiContinuousUpperFactor s = linearSieveUpperFactor s := by
  have h := mul_suzukiProposition118SourceTPlus_eq_amplitude_sub hH hs1 hs3
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract hH] at h
  unfold suzukiContinuousUpperFactor linearSieveUpperFactor
  apply (eq_div_iff (by linarith : s ≠ 0)).mpr
  rw [add_mul,one_mul,mul_comm (suzukiProposition118SourceTPlus s),h]
  ring

private theorem rosser_suzuki_lower_first {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) {s : ℝ} (hs2 : 2≤s) (hs4 : s≤4) :
    suzukiContinuousLowerFactor s = linearSieveLowerFactor s := by
  unfold suzukiContinuousLowerFactor suzukiContinuousLowerTail linearSieveLowerFactor
  rw [one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval hH hs2 hs4,
    suzukiLowerSieveFactorFirstInterval_eq_log hs2 hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract hH]

/-- Uniform first-interval comparison at an integer level, for every finite sieve
with the same dimension-one product constant. Both signs use the same error. -/
theorem rosser_first_interval_uniform (K : ℝ) (hK : 2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve) (s : ℝ),
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D:ℝ)^(1/s)⌉₊) →
      (1<s → s≤3 → linearSieveMain true S.prodPrimes D S.nu ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (linearSieveUpperFactor s + C*(Real.log D)^(-(1/2:ℝ)))) ∧
      (2≤s → s≤4 → AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (linearSieveLowerFactor s - C*(Real.log D)^(-(1/2:ℝ))) ≤
          linearSieveMain false S.prodPrimes D S.nu) := by
  let H := jr1965Section13HatLayers
  have hH : Section13HatSourceContract H := jr1965Section13HatSourceContract
  obtain ⟨c₁,_,hc₁⟩ := exists_upperRosserDensity_at_natCeil_above_one H hH basePoint_source_parameters
  obtain ⟨_,_,A,_,_,hA,hu⟩ := hc₁ c₁ le_rfl
  obtain ⟨c₂,_,hc₂⟩ :=
    exists_lowerRosserDensity_continuousLowerFactor_of_suzuki_literal_allDepth_uniform_in_S_of_source
      H hH basePoint_source_parameters
  obtain ⟨_,_,B,_,_,hB,hl⟩ := hc₂ c₂ le_rfl
  obtain ⟨T,hT,henv⟩ := rosser_uniform_error_envelope H hH.toSection13HatContract
  let C := max A B * Real.exp (Real.sqrt K) * T
  have hA0 : 0<A := by linarith
  have hB0 : 0<B := by linarith
  have hmax : 0<max A B := hA0.trans_le (le_max_left _ _)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  filter_upwards [basePoint_large_geometry] with D hD
  intro S s hlocal hcut
  have hDr : (1:ℝ)<D := by exact_mod_cast (show 1<D by omega)
  have hpow := Real.rpow_nonneg (Real.log_nonneg hDr.le) (-(1/2:ℝ))
  have herr {c : ℝ} (hc : c≤max A B) (hc0 : 0≤c) (depth : ℕ)
      (hs1 : 1≤s) (hs4 : s≤4) :
      c*Real.exp (Real.sqrt K)*errorEnvelope H depth D 16 s*(Real.log D)^(-(1/2:ℝ)) ≤
        C*(Real.log D)^(-(1/2:ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hpow
    calc _ ≤ c*Real.exp (Real.sqrt K)*T :=
           mul_le_mul_of_nonneg_left (henv depth hDr hD.2.2 hs1 hs4) (by positivity)
         _ ≤ C := mul_le_mul_of_nonneg_right
           (mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le) hT.le
  constructor
  · intro hs1 hs3
    have hs4 : s≤4 := by linarith
    have hZ := (basePoint_cutoff_bounds hD.1 hs1.le).1
    have h := hu S K hK hlocal D hD.1 s hs1 hs4 (hs4.trans hD.2.1) hZ hcut
    rw [linearSieveMain_matches_suzuki_upper, ←rosser_suzuki_upper_first hH hs1 hs3]
    apply h.trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add_right (herr (le_max_left _ _) hA0.le _ hs1.le hs4) _)
      (basePoint_products_nonneg S)
  · intro hs2 hs4
    have hs1 : 1≤s := by linarith
    have hZ := (basePoint_cutoff_bounds hD.1 hs1).1
    let z := ⌈(D:ℝ)^(1/s)⌉₊
    have h := hl S K hK hlocal D hD.1 s hs2 (hs4.trans hD.2.1) hZ
    have hbridge := basePoint_lower_carrier S D z hcut
    rw [linearSieveMain_matches_suzuki_lower, hbridge.1, ←hbridge.2,
      ←rosser_suzuki_lower_first hH hs2 hs4]
    apply le_trans _ h
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (herr (le_max_right _ _) hB0.le _ hs1 hs4) _)
      (suzukiVProduct_pos S (z:ℝ)).le

/-- The same two comparisons with both first intervals closed. -/
theorem rosser_first_intervals_closed_uniform (K : ℝ) (hK : 2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve) (s : ℝ),
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D:ℝ)^(1/s)⌉₊) →
      (1≤s → s≤3 → linearSieveMain true S.prodPrimes D S.nu ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (linearSieveUpperFactor s + C*(Real.log D)^(-(1/2:ℝ)))) ∧
      (2≤s → s≤4 → AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
        (linearSieveLowerFactor s - C*(Real.log D)^(-(1/2:ℝ))) ≤
          linearSieveMain false S.prodPrimes D S.nu) := by
  obtain ⟨C,hC,he⟩ := rosser_first_interval_uniform K hK
  refine ⟨C,hC,?_⟩
  filter_upwards [he,eventually_ge_atTop 2] with D hD hD2
  intro S s hlocal hcut
  refine ⟨?_,(hD S s hlocal hcut).2⟩
  intro hs1 hs3
  rcases hs1.eq_or_lt with heq | hlt
  · subst s
    apply rosser_upper_at_one_of_right hD2 hcut
    intro t ht ht3 hps
    exact (hD S t hlocal hps).1 ht ht3
  · exact (hD S s hlocal hcut).1 hlt hs3

/-- At s = 3 the upper main polynomial has the sharp constant 2 e^γ / 3. -/
theorem rosser_upper_base_three (K : ℝ) (hK : 2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve),
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D:ℝ)^(1/(3:ℝ))⌉₊) →
      linearSieveMain true S.prodPrimes D S.nu ≤
        AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (linearSieveUpperFactor 3 + C*(Real.log D)^(-(1/2:ℝ))) := by
  obtain ⟨C,hC,he⟩ := rosser_first_interval_uniform K hK
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with D hD
  intro S hK hcut
  exact (hD S 3 hK hcut).1 (by norm_num) (by norm_num)

/-- At s = 4 the lower main polynomial has constant 2 e^γ log 3 / 4. -/
theorem rosser_lower_base_four (K : ℝ) (hK : 2≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ D : ℕ in atTop, ∀ (S : BoundingSieve),
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, p < ⌈(D:ℝ)^(1/(4:ℝ))⌉₊) →
      AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S *
          (linearSieveLowerFactor 4 - C*(Real.log D)^(-(1/2:ℝ))) ≤
        linearSieveMain false S.prodPrimes D S.nu := by
  obtain ⟨C,hC,he⟩ := rosser_first_interval_uniform K hK
  refine ⟨C,hC,?_⟩
  filter_upwards [he] with D hD
  intro S hK hcut
  exact (hD S 4 hK hcut).2 (by norm_num) le_rfl

end FareyGoldbach
