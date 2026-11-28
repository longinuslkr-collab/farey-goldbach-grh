import FareyGoldbach.ChenAPProfiles

/-! # A common medium-prime majorant after omitting divisors of a multiple of the target -/

namespace FareyGoldbach

noncomputable def chenAPMediumMass (N : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    if q∣N then 0 else chenDivisorDensity q

noncomputable def chenAPMediumScale (N : ℕ) : ℝ :=
  Real.exp Real.eulerMascheroniConstant*(Real.log (chenLowerCutoff N:ℝ)/Real.log (N:ℝ))

theorem chenAP_medium_envelope {θ δ : ℝ} (hθ : 11/24<θ) (hδ : 0≤δ)
    {N m : ℕ} (hN : 2^24≤N) (hNm : N∣m)
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
      (chenAPMediumScale N*chenMediumIdealSum θ N+
        δ*(chenAPMediumScale N+1)*chenAPMediumMass N) := by
  let z := chenLowerCutoff N
  let D := chenPowerLevel θ N
  let C := chenAPMediumScale N
  let V := chenDensityProduct m z
  let L := Real.log (N:ℝ)
  let P := chenMediumPrimes z (chenUpperCutoff N)
  let K (q : ℕ) := 2/(θ-Real.log (q:ℝ)/L)
  let g (q : ℕ) := if q∣N then 0 else chenDivisorDensity q
  let I (q : ℕ) := if q∣N then 0 else chenDivisorDensity q*K q
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
    by_cases hqN : q∣N
    · simp [I,g,hqN,hqN.trans hNm]
    simp only [I,g,ite_eq_right hqN]
    by_cases hqm : q∣m
    · rw [ite_eq_left hqm]
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
         _ = _ := by ring
  calc _ ≤ ∑ q∈P, V*(C*I q+δ*(C+1)*g q) := Finset.sum_le_sum hpoint
       _ = _ := by
         rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
         rfl

end FareyGoldbach
