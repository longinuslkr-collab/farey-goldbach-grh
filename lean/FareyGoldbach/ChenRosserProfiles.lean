import FareyGoldbach.ChenBoundingSieve
import FareyGoldbach.ChenCanonicalComparisons
import FareyGoldbach.ChenDimensionOne

/-! # Uniform passage from Rosser bounds to Chen's integer cutoffs -/

open Filter Set
open scoped Topology

namespace FareyGoldbach

theorem chenBoundingSieve_dimension_one :
    ∃ K : ℝ, 2≤K ∧ ∀ (N w : ℕ) (he : Even N) (a b : ℝ), 2≤a → a≤b →
      ∏ p ∈ (chenBoundingSieve he w).prodPrimes.primeFactors.filter
        (fun p : ℕ => a≤(p:ℝ) ∧ (p:ℝ)<b), (1-(chenBoundingSieve he w).nu p)⁻¹ ≤
        Real.log b/Real.log a*(1+K/Real.log a) := by
  obtain ⟨K,hK,hbound⟩ := chen_inverse_interval_dimension_one
  refine ⟨max K 2,le_max_right ..,?_⟩
  intro N w he a b ha hab
  let s := (chenSiftingPrimes N w).filter (fun p : ℕ => a≤(p:ℝ) ∧ (p:ℝ)<b)
  have hs (p : ℕ) (hp : p∈s) : p.Prime ∧ 2<p := by
    have hp' := (Finset.mem_filter.mp hp).1
    exact ⟨(Finset.mem_filter.mp hp').2.1,three_le_of_mem_chenSiftingPrimes he hp'⟩
  have hb := hbound s hs a b ha hab (fun p hp => (Finset.mem_filter.mp hp).2)
  simp only [chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors,chenBoundingSieve_nu]
  change ∏ p∈s, (1-chenDivisorDensity p)⁻¹ ≤ _
  have hprod : (∏ p∈s, (1-chenDivisorDensity p)⁻¹) = ∏ p∈s, (1-1/((p:ℝ)-1))⁻¹ := by
    apply Finset.prod_congr rfl
    intro p hp
    have h := (hs p hp).1
    simp [chenDivisorDensity,Nat.totient_prime h,Nat.cast_sub h.one_le]
  rw [hprod]
  apply hb.trans
  have hpa := Real.log_pos (by linarith : (1:ℝ)<a)
  have hpb := Real.log_pos (by linarith : (1:ℝ)<b)
  exact mul_le_mul_of_nonneg_left
    (add_le_add_right (div_le_div_of_nonneg_right (le_max_left K 2) hpa.le) _)
    (div_nonneg hpb.le hpa.le)

private theorem chenDensityProduct_nonnegative (N w : ℕ) : 0≤chenDensityProduct N w := by
  unfold chenDensityProduct
  apply Finset.prod_nonneg
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).2.1
  have hφ : (1:ℝ)≤p.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hp'.pos)
  exact sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one hφ |>.trans_eq (by norm_num))

/-- A single uniform bound supplies the three profiles, even for all medium-prime
quotients at once. Those quotients tend to infinity uniformly in the prime. -/
theorem chenFloorRosserProfiles_of_uniform {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (hbase : ∃ C : ℝ, 0<C ∧ ∀ᶠ D : ℕ in atTop, ∀ (N w : ℕ), Even N →
      2≤w → w=⌈(D:ℝ)^(1/chenSieveParameter D w)⌉₊ →
      (1<chenSieveParameter D w → chenSieveParameter D w≤3 →
        linearSieveMain true (chenSiftingProduct N w) D chenDivisorDensity ≤
          chenDensityProduct N w*(linearSieveUpperFactor (chenSieveParameter D w)+
            C*(Real.log (D:ℝ))^(-(1/2:ℝ)))) ∧
      (2≤chenSieveParameter D w → chenSieveParameter D w≤4 →
        chenDensityProduct N w*(linearSieveLowerFactor (chenSieveParameter D w)-
          C*(Real.log (D:ℝ))^(-(1/2:ℝ))) ≤
            linearSieveMain false (chenSiftingProduct N w) D chenDivisorDensity)) :
    ChenFloorRosserProfiles θ := by
  intro ε hε
  obtain ⟨C,_,hbase⟩ := hbase
  have hzero : Tendsto (fun D : ℕ => C*(Real.log (D:ℝ))^(-(1/2:ℝ))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    simpa only [mul_zero,Function.comp_apply] using ht.const_mul C
  obtain ⟨D₀,hD⟩ := eventually_atTop.1
    (hbase.and (hzero.eventually_lt_const hε))
  have hz := (chenPowerLevel_tendsto_atTop (a:=1/8) (by norm_num)).eventually_ge_atTop (max D₀ 2)
  have hD' := (chenPowerLevel_tendsto_atTop (a:=θ) (by linarith)).eventually_ge_atTop (max D₀ 2)
  apply eventually_inf_principal.mpr
  filter_upwards [hz,hD',eventually_ge_atTop (2^24:ℕ),chenActualSieveParameters_eventually_mem hθ hθ₂,
    chenUpperParameters_eventually_gt_one hθ] with N hz hD' hN hparams hopen he
  let D := chenPowerLevel θ N
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  have hzD : D₀≤z := (le_max_left ..).trans hz
  have hD₀ : D₀≤D := (le_max_left ..).trans hD'
  have hD₂ : 2≤D := (le_max_right ..).trans hD'
  obtain ⟨hz₂,hy₂,_⟩ := chenPowerLevel_cutoffs hθ hN
  have hbz := (hD D hD₀).1 N z he hz₂ (chenSieveParameter_cutoff hD₂ hz₂).symm
  have hby := (hD D hD₀).1 N y he hy₂ (chenSieveParameter_cutoff hD₂ hy₂).symm
  have herr := (hD D hD₀).2.le
  change chenDensityProduct N z*(linearSieveLowerFactor (chenSieveParameter D z)-ε)≤
      chenLowerPolynomial θ N ∧
    chenSwitchedPolynomial θ N≤chenDensityProduct N y*(linearSieveUpperFactor (chenSieveParameter D y)+ε) ∧ _
  refine ⟨?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_left (sub_le_sub_left herr _) (chenDensityProduct_nonnegative _ _)).trans
      (hbz.2 hparams.1.1 hparams.1.2)
  · exact (hby.1 hopen.1 hparams.2.1.2).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right herr _) (chenDensityProduct_nonnegative _ _))
  · intro q hq
    have hzq := chen_mediumNat_div_ge_lower hθ hN hq
    have hq₀ : D₀≤D/q := hzD.trans hzq
    have hq₂ : 2≤D/q := hz₂.trans hzq
    have hbq := (hD (D/q) hq₀).1 N z he hz₂ (chenSieveParameter_cutoff hq₂ hz₂).symm
    exact (hbq.1 (hopen.2 q hq) (hparams.2.2 q hq).2).trans
      (mul_le_mul_of_nonneg_left (add_le_add_right (hD (D/q) hq₀).2.le _)
        (chenDensityProduct_nonnegative _ _))

end FareyGoldbach
