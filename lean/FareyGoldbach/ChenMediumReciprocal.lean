import FareyGoldbach.ChenMediumQuadrature
import FareyGoldbach.ChenMertens

/-! # The medium-prime reciprocal term in Chen's sieve -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- The unweighted reciprocal-totient mass used to bound uniform errors in each profile. -/
theorem chen_medium_totient_tendsto :
    Tendsto (fun N : ℕ => ∑ q ∈ chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      if q∣N then (0:ℝ) else 1/(q.totient:ℝ)) atTop (𝓝 (Real.log (8/3))) := by
  have h := chen_band_mass_tendsto_of_mertens chen_prime_reciprocal_mertens
    (by norm_num : (0:ℝ)<1/8) (by norm_num : (1/8:ℝ)≤1/3)
  rw [←Real.log_div (by norm_num : (1/3:ℝ)≠0) (by norm_num : (1/8:ℝ)≠0),
    show (1/3:ℝ)/(1/8)=8/3 by norm_num] at h
  apply h.congr
  intro N
  unfold chenMediumPrimes
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : q.Prime
  · by_cases hd : q∣N <;> simp [chenBandWeight,hp,hd]
  · simp [chenBandWeight,hp]

/-- The local reciprocal kernel on an arbitrary fixed exponent band. -/
theorem chen_prime_reciprocal_kernel_tendsto {a b θ : ℝ} (ha:0<a) (hab:a<b) (hθ:b<θ) :
    Tendsto (fun N : ℕ => ∑ q ∈ chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel b N),
      if q∣N then (0:ℝ) else (1/(q.totient:ℝ))*(2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))))
      atTop (𝓝 (∫ u in a..b, 2/(u*(θ-u)))) := by
  refine (chen_weighted_band_between_tendsto_of_mertens chen_prime_reciprocal_mertens ha hab.le hθ).congr fun N => ?_
  unfold chenWeightedBandBetween chenMediumPrimes
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hp : q.Prime
  · by_cases hd : q∣N <;> simp [chenLogWeight,chenBandWeight,hp,hd,mul_comm]
  · simp [chenBandWeight,hp]

/-- The actual weighted medium-prime sum converges, including both integer cutoffs,
the omitted divisors of N, and the replacement of p by φ(p) in each local factor. -/
theorem chen_medium_reciprocal_tendsto {θ : ℝ} (hθ : 1/3<θ) :
    Tendsto (fun N : ℕ => ∑ q ∈ chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      if q∣N then (0:ℝ) else (1/(q.totient:ℝ))*(2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))))
      atTop (𝓝 (chenMediumMainCoeff θ)) := by
  rw [←chen_medium_integral_eq hθ]
  exact chen_prime_reciprocal_kernel_tendsto (by norm_num) (by norm_num) hθ

/-- The general band kernel comes from the same primitive at both endpoints. -/
theorem chen_prime_band_kernel_integral_eq {a b θ : ℝ} (ha:0<a) (hab:a≤b) (hθ:b<θ) :
    (∫ u in a..b, 2/(u*(θ-u))) = (2/θ)*Real.log ((b/(θ-b))/(a/(θ-a))) := by
  let F (t : ℝ) := (2/θ)*(Real.log t-Real.log (θ-t))
  have hθ₀ : 0<θ := by linarith
  have hD (t:ℝ) (ht:t∈Set.uIcc a b) : HasDerivAt F (2/(t*(θ-t))) t := by
    rw [Set.uIcc_of_le hab] at ht
    have ht₀ := ha.trans_le ht.1
    have hsub : 0<θ-t := by linarith [ht.2]
    have hid : HasDerivAt (fun x:ℝ => x) 1 t := hasDerivAt_id _
    have hsub' : HasDerivAt (fun x:ℝ => θ-x) (-1) t := hid.const_sub θ
    convert ((Real.hasDerivAt_log ht₀.ne').sub (hsub'.log hsub.ne')).const_mul (2/θ) using 1
    field_simp; ring
  have hI : IntervalIntegrable (fun t:ℝ => 2/(t*(θ-t))) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    have ht₀ := ha.trans_le ht.1
    have hsub : 0<θ-t := by linarith [ht.2]
    fun_prop (disch := positivity)
  have hb := ha.trans_le hab
  have h₁ := sub_pos.mpr hθ
  have h₂ := sub_pos.mpr (hab.trans_lt hθ)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hI,Real.log_div (x:=b/(θ-b)) (y:=a/(θ-a)) (by positivity) (by positivity),
    Real.log_div hb.ne' h₁.ne',Real.log_div ha.ne' h₂.ne']
  dsimp [F]; ring

/-- The loss from θ/4 to 1/8 converts the coefficient at sieve parameter 4 into
the physical lower coefficient. -/
theorem chen_lower_buchstab_integral_eq {θ : ℝ} (hθ:11/24<θ) (hhalf:θ≤1/2) :
    (2/θ)*Real.log 3-(∫ u in θ/4..(1/8:ℝ), 2/(u*(θ-u))) = chenLowerMainCoeff θ := by
  have ht : 0<θ := by linarith
  have hm : 0<8*θ-1 := by linarith
  rw [chen_prime_band_kernel_integral_eq (by positivity) (by linarith) (by linarith)]
  have he : ((1/8)/(θ-1/8))/((θ/4)/(θ-θ/4))=3/(8*θ-1) := by
    field_simp [show θ-1/8≠0 by linarith,show θ-θ/4≠0 by linarith]
    ring
  rw [he,Real.log_div (by norm_num) hm.ne']
  unfold chenLowerMainCoeff
  ring

end FareyGoldbach
