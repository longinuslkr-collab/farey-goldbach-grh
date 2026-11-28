import FareyGoldbach.ChenAPComparisons

/-! # Restoring medium primes which divide the source size -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

noncomputable def twinChenMediumMass (M : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M), chenDivisorDensity q

noncomputable def twinChenMediumIdeal (θ : ℝ) (M : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M),
    chenDivisorDensity q*(2/(θ-Real.log (q:ℝ)/Real.log (M:ℝ)))

private theorem restore_medium_tendsto (f : ℕ→ℕ→ℝ) {c A : ℝ} (hA : 0≤A)
    (hf : ∀ᶠ M : ℕ in atTop, ∀ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M),
      0≤f M q ∧ f M q≤A)
    (h : Tendsto (fun M => ∑ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M),
      if q∣M then 0 else chenDivisorDensity q*f M q) atTop (𝓝 c)) :
    Tendsto (fun M => ∑ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M),
      chenDivisorDensity q*f M q) atTop (𝓝 c) := by
  have hsmall := (chenLogTwo_div_powerLevel_tendsto (by norm_num : (0:ℝ)<1/8)).const_mul (4*A)
  rw [mul_zero] at hsmall
  have hup := h.add hsmall
  rw [add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h hup
  · filter_upwards [hf] with M hf
    apply sum_le_sum
    intro q hq
    split_ifs
    · exact mul_nonneg (by unfold chenDivisorDensity; positivity) (hf q hq).1
    · exact le_rfl
  filter_upwards [hf,eventually_ge_atTop (1:ℕ),
    (chenPowerLevel_tendsto_atTop (by norm_num : (0:ℝ)<1/8)).eventually_ge_atTop 2] with M hf hM hz
  let z := chenLowerCutoff M
  let P := chenMediumPrimes z (chenUpperCutoff M)
  let B := P.filter (fun q => q∣M)
  have hzr : (2:ℝ)≤z := by exact_mod_cast hz
  have hz₀ : (0:ℝ)<z := by linarith
  have hpt (q : ℕ) (hq : q∈P) :
      chenDivisorDensity q*f M q ≤ (if q∣M then 0 else chenDivisorDensity q*f M q)
        + (if q∣M then 2/(z:ℝ)*A else 0) := by
    by_cases hd : q∣M
    · simp only [hd,ite_true,zero_add]
      obtain ⟨hI,hpr⟩ := mem_filter.mp hq
      have hqz : (z:ℝ)≤q := Nat.cast_le.mpr (mem_Ico.mp hI).1
      have hq' : 0<(q:ℝ)-1 := by linarith
      have hg : chenDivisorDensity q≤2/(z:ℝ) := by
        unfold chenDivisorDensity
        rw [Nat.totient_prime hpr,Nat.cast_sub hpr.one_le,Nat.cast_one]
        exact (div_le_div_iff₀ hq' hz₀).mpr (by linarith)
      exact mul_le_mul hg (hf q hq).2 (hf q hq).1 (by positivity)
    · simp [hd]
  have hcard : (B.card:ℝ)≤2*Real.log (2*(M:ℝ)) := by
    apply le_trans _ (primeFactors_card_le_two_log hM)
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro q hq
    obtain ⟨hp,hd⟩ := mem_filter.mp hq
    exact Nat.mem_primeFactors.mpr ⟨(mem_filter.mp hp).2,hd,by omega⟩
  have hrest : (∑ q∈P, if q∣M then 2/(z:ℝ)*A else 0)=(B.card:ℝ)*(2/(z:ℝ)*A) := by
    simp [B,Finset.sum_ite]
  have hs := sum_le_sum hpt
  rw [sum_add_distrib,hrest] at hs
  apply hs.trans (add_le_add le_rfl ?_)
  calc (B.card:ℝ)*(2/(z:ℝ)*A) ≤ (2*Real.log (2*(M:ℝ)))*(2/(z:ℝ)*A) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by change _ = 4*A*(Real.log (2*(M:ℝ))/(z:ℝ)); ring

theorem twinChenMediumMass_tendsto :
    Tendsto twinChenMediumMass atTop (𝓝 (Real.log (8/3))) := by
  unfold twinChenMediumMass
  simpa only [mul_one] using restore_medium_tendsto (fun _ _ => 1) zero_le_one
    (Eventually.of_forall fun _ _ _ => ⟨zero_le_one,le_rfl⟩)
    (by simpa [chenDivisorDensity] using chen_medium_totient_tendsto)

theorem twinChenMediumIdeal_tendsto {θ : ℝ} (hθ : 1/3<θ) :
    Tendsto (twinChenMediumIdeal θ) atTop (𝓝 (chenMediumMainCoeff θ)) := by
  apply restore_medium_tendsto _ (show 0≤2/(θ-1/3) from div_nonneg (by norm_num) (sub_pos.mpr hθ).le)
    _ (chen_medium_reciprocal_tendsto hθ)
  filter_upwards [eventually_ge_atTop (2:ℕ)] with M hM q hq
  have hh := (chenMediumLogPrimeRatio_bounds hM hq).2
  have hd : 0<θ-Real.log (q:ℝ)/Real.log (M:ℝ) := by linarith
  exact ⟨div_nonneg (by norm_num) hd.le,div_le_div_of_nonneg_left (by norm_num)
    (sub_pos.mpr hθ) (sub_le_sub_left hh _)⟩

theorem twinChen_medium_envelope {θ δ : ℝ} (hθ : 11/24<θ) (hδ : 0≤δ)
    {N m : ℕ} (hN : 2^24≤N)
    (hP : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      linearSieveMain true (chenSiftingProduct m (chenLowerCutoff N)) (chenPowerLevel θ N/q) chenDivisorDensity ≤
        chenDensityProduct m (chenLowerCutoff N)*
          (linearSieveUpperFactor (chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))+δ))
    (h₁ : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      1≤chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))
    (h₂ : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      2/(Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ)) ≤
        2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))+δ) :
    chenAPMediumPolynomial θ N m ≤ chenDensityProduct m (chenLowerCutoff N)*
      (chenAPMediumScale N*twinChenMediumIdeal θ N+
        δ*(chenAPMediumScale N+1)*twinChenMediumMass N) := by
  let z := chenLowerCutoff N
  let D := chenPowerLevel θ N
  let C := chenAPMediumScale N
  let V := chenDensityProduct m z
  let L := Real.log (N:ℝ)
  let P := chenMediumPrimes z (chenUpperCutoff N)
  let K (q : ℕ) := 2/(θ-Real.log (q:ℝ)/L)
  let g (q : ℕ) := chenDivisorDensity q
  let I (q : ℕ) := chenDivisorDensity q*K q
  have hn₂ : 2≤N := by omega
  have hn : (2:ℝ)≤N := by exact_mod_cast hn₂
  have hL : 0<L := Real.log_pos (by linarith)
  have hz₂ := (chenPowerLevel_cutoffs hθ hN).1
  have hzR : (2:ℝ)≤z := by exact_mod_cast hz₂
  have hzL : 0<Real.log (z:ℝ) := Real.log_pos (by linarith)
  have hC : 0≤C := mul_nonneg (Real.exp_pos _).le (div_nonneg hzL.le hL.le)
  have hV : 0≤V := chenAP_density_nonneg .. 
  have hpoint (q : ℕ) (hq : q∈P) :
      (if q∣m then 0 else chenDivisorDensity q*
        linearSieveMain true (chenSiftingProduct m z) (D/q) chenDivisorDensity) ≤
      V*(C*I q+δ*(C+1)*g q) := by
    have hg : 0≤chenDivisorDensity q := by unfold chenDivisorDensity; positivity
    have hr := (chenMediumLogPrimeRatio_bounds hn₂ hq).2
    have hden : 0<θ-Real.log (q:ℝ)/L := by dsimp [L]; linarith
    have hK : 0≤K q := div_nonneg (by norm_num) hden.le
    by_cases hqm : q∣m
    · rw [ite_eq_left hqm]
      dsimp only [I,g]
      positivity
    rw [ite_eq_right hqm]
    have hqD : 0<Real.log ((D/q:ℕ):ℝ) :=
      hzL.trans_le ((one_le_div hzL).mp (h₁ q hq))
    have hident : linearSieveUpperFactor (chenSieveParameter (D/q) z)=
        C*(2/(Real.log ((D/q:ℕ):ℝ)/L)) := by
      change linearSieveUpperFactor (chenSieveParameter (D/q) z)=
        Real.exp Real.eulerMascheroniConstant*(Real.log (z:ℝ)/L)*(2/(Real.log ((D/q:ℕ):ℝ)/L))
      unfold linearSieveUpperFactor chenSieveParameter
      field_simp
    have hker : linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ≤C*K q+δ*(C+1) := by
      rw [hident]
      have hb := mul_le_mul_of_nonneg_left (h₂ q hq) hC
      change C*(2/(Real.log ((D/q:ℕ):ℝ)/L))≤C*(K q+δ) at hb
      linarith only [hb]
    calc _ ≤ chenDivisorDensity q*(V*(C*K q+δ*(C+1))) :=
          mul_le_mul_of_nonneg_left ((hP q hq).trans (mul_le_mul_of_nonneg_left hker hV)) hg
         _ = _ := by dsimp only [I,g]; ring
  calc _ ≤ ∑ q∈P, V*(C*I q+δ*(C+1)*g q) := Finset.sum_le_sum hpoint
       _ = _ := by
         rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
         rfl

end FareyGoldbach
