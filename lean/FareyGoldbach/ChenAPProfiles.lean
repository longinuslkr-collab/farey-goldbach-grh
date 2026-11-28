import FareyGoldbach.ChenUnconditionalComparisons

/-! # Rosser profiles with independent sieve target and cutoff size -/

open Filter Set
open scoped Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace FareyGoldbach

noncomputable def chenAPLowerPolynomial (θ : ℝ) (N m : ℕ) : ℝ :=
  linearSieveMain false (chenSiftingProduct m (chenLowerCutoff N)) (chenPowerLevel θ N) chenDivisorDensity

noncomputable def chenAPMediumPolynomial (θ : ℝ) (N m : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    if q∣m then 0 else chenDivisorDensity q*
      linearSieveMain true (chenSiftingProduct m (chenLowerCutoff N)) (chenPowerLevel θ N/q) chenDivisorDensity

noncomputable def chenAPSwitchedPolynomial (θ : ℝ) (N m : ℕ) : ℝ :=
  linearSieveMain true (chenSiftingProduct m (chenUpperCutoff N)) (chenPowerLevel θ N) chenDivisorDensity

theorem chenAP_density_nonneg (m w : ℕ) : 0≤chenDensityProduct m w := by
  unfold chenDensityProduct
  apply Finset.prod_nonneg
  intro p hp
  have hφ : (1:ℝ)≤p.totient := Nat.one_le_cast.mpr
    (Nat.totient_pos.mpr (Finset.mem_filter.mp hp).2.1.pos)
  exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hφ)).2 hφ)

private theorem chenAP_uniform_profile {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ D : ℕ in atTop, ∀ m w : ℕ, Even m → 2≤w → 2≤D →
      (1<chenSieveParameter D w → chenSieveParameter D w≤3 →
        linearSieveMain true (chenSiftingProduct m w) D chenDivisorDensity ≤
          chenDensityProduct m w*(linearSieveUpperFactor (chenSieveParameter D w)+ε)) ∧
      (2≤chenSieveParameter D w → chenSieveParameter D w≤4 →
        chenDensityProduct m w*(linearSieveLowerFactor (chenSieveParameter D w)-ε)≤
          linearSieveMain false (chenSiftingProduct m w) D chenDivisorDensity) := by
  obtain ⟨K,hK,hlocal⟩ := chenBoundingSieve_dimension_one
  obtain ⟨C,_,hbase⟩ := rosser_first_interval_uniform K hK
  have hzero : Tendsto (fun D : ℕ => C*(Real.log (D:ℝ))^(-(1/2:ℝ))) atTop (𝓝 0) := by
    have ht := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    simpa only [mul_zero,Function.comp_apply] using ht.const_mul C
  filter_upwards [hbase,hzero.eventually_lt_const hε] with D hD herr m w he hw hD₂
  let S := chenBoundingSieve he w
  have hdim : HasDimensionOneLocalProductBound S K := hlocal m w he
  have hcut (p : ℕ) (hp : p∈S.prodPrimes.primeFactors) : p<⌈(D:ℝ)^(1/chenSieveParameter D w)⌉₊ := by
    rw [chenSieveParameter_cutoff hD₂ hw]
    apply chenSiftingPrime_lt_cutoff (N:=m)
    simpa only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors] using hp
  have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S=chenDensityProduct m w := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors chenDensityProduct
    simp only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors,chenBoundingSieve_nu,
      chenDivisorDensity]
  have hν : (S.nu : ℕ→ℝ)=chenDivisorDensity := rfl
  have hh := hD S (chenSieveParameter D w) hdim hcut
  simp only [hV,hν,S,chenBoundingSieve_prodPrimes] at hh
  exact ⟨fun h₁ h₂ => (hh.1 h₁ h₂).trans (mul_le_mul_of_nonneg_left
      (add_le_add_right herr.le _) (chenAP_density_nonneg _ _)),
    fun h₁ h₂ => (mul_le_mul_of_nonneg_left
      (sub_le_sub_left herr.le _) (chenAP_density_nonneg _ _)).trans (hh.2 h₁ h₂)⟩

theorem chenAP_floor_profiles {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, Even m →
      let D := chenPowerLevel θ N
      let z := chenLowerCutoff N
      let y := chenUpperCutoff N
      chenDensityProduct m z*(linearSieveLowerFactor (chenSieveParameter D z)-ε)≤chenAPLowerPolynomial θ N m ∧
      chenAPSwitchedPolynomial θ N m≤chenDensityProduct m y*(linearSieveUpperFactor (chenSieveParameter D y)+ε) ∧
      ∀ q∈chenMediumPrimes z y, linearSieveMain true (chenSiftingProduct m z) (D/q) chenDivisorDensity ≤
        chenDensityProduct m z*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+ε) := by
  obtain ⟨D₀,hD⟩ := eventually_atTop.1 (chenAP_uniform_profile hε)
  have hz := (chenPowerLevel_tendsto_atTop (a:=1/8) (by norm_num)).eventually_ge_atTop (max D₀ 2)
  have hD' := (chenPowerLevel_tendsto_atTop (a:=θ) (by linarith)).eventually_ge_atTop (max D₀ 2)
  filter_upwards [hz,hD',eventually_ge_atTop (2^24:ℕ),chenActualSieveParameters_eventually_mem hθ hθ₂,
    chenUpperParameters_eventually_gt_one hθ] with N hz hD' hN hparams hopen m he
  let D := chenPowerLevel θ N
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  have hzD : D₀≤z := (le_max_left ..).trans hz
  have hD₀ : D₀≤D := (le_max_left ..).trans hD'
  have hD₂ : 2≤D := (le_max_right ..).trans hD'
  obtain ⟨hz₂,hy₂,_⟩ := chenPowerLevel_cutoffs hθ hN
  refine ⟨(hD D hD₀ m z he hz₂ hD₂).2 hparams.1.1 hparams.1.2,
    (hD D hD₀ m y he hy₂ hD₂).1 hopen.1 hparams.2.1.2,?_⟩
  intro q hq
  have hdiv := chen_mediumNat_div_ge_lower hθ hN hq
  exact (hD (D/q) (hzD.trans hdiv) m z he hz₂ (hz₂.trans hdiv)).1 (hopen.2 q hq) (hparams.2.2 q hq).2

end FareyGoldbach
