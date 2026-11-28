import FareyGoldbach.ChenTheoremUnconditional
import FareyGoldbach.ChenSwitchingScales

/-! # A lower sieve at cutoffs just below a quarter power -/

open Filter Set
open scoped Classical Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace FareyGoldbach

/-- Sifted prime complements after removing units, common factors, square
factors and prime summands below the second cutoff. -/
noncomputable def chenRoughThreeClean (N z y : ℕ) : Finset ℕ :=
  chenSifted N z (chenA N) \ chenBadSet N z y

theorem mem_chenRoughThreeClean_iff {N z y m : ℕ} :
    m ∈ chenRoughThreeClean N z y ↔
      m ≤ N ∧ (N - m).Prime ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        IsRough z m ∧ y ≤ N - m := by
  constructor
  · intro hm
    obtain ⟨hs, hb⟩ := Finset.mem_sdiff.mp hm
    obtain ⟨hA, hr⟩ := Finset.mem_filter.mp hs
    obtain ⟨hbound, hp⟩ := Finset.mem_filter.mp hA
    have hgood : ¬(m < 2 ∨ ¬m.Coprime N ∨ ¬Squarefree m ∨ N - m < y) :=
      fun h ↦ hb (Finset.mem_filter.mpr ⟨hs, h⟩)
    push Not at hgood
    obtain ⟨hm, hcop, hsq, hy⟩ := hgood
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp hbound), hp, by omega, hsq, hcop,
      chenRough_primeFactors hr hcop, hy⟩
  · rintro ⟨hmN, hp, hm, hsq, hcop, hr, hy⟩
    have hs : m ∈ chenSifted N z (chenA N) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩, ?_⟩
      intro q hq hqp _ hqd
      exact (not_lt_of_ge (hr q (Nat.mem_primeFactors.mpr ⟨hqp, hqd, by omega⟩)))
        (Finset.mem_range.mp hq)
    refine Finset.mem_sdiff.mpr ⟨hs, fun hb ↦ ?_⟩
    rcases (Finset.mem_filter.mp hb).2 with hl | hc | hsf | hyp
    · omega
    · exact hc hcop
    · exact hsf hsq
    · omega

private theorem roughThree_bad_card_le_eighth {N z y : ℕ}
    (hz : chenLowerCutoff N ≤ z) (hy : y ≤ chenUpperCutoff N) :
    ((chenBadSet N z y).card : ℝ) ≤ chenElementaryError N := by
  apply Nat.cast_le.mpr (Finset.card_le_card ?_)
  intro m hm
  obtain ⟨hs, hb⟩ := Finset.mem_filter.mp hm
  obtain ⟨hA, hr⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hA, ?_⟩, ?_⟩
  · intro q hq
    exact hr q (Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hz))
  · rcases hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (h.trans_le hy)))

private theorem roughThree_finite_lower {N z D : ℕ} (hzD : z ≤ D) (hD : 1 < D) :
    ((chenA N).card : ℝ) * linearSieveMain false (chenSiftingProduct N z) D chenDivisorDensity -
      chenReducedError N D (chenPrimeAPError N) ≤ ((chenSifted N z (chenA N)).card : ℝ) := by
  let P := chenSiftingProduct N z
  have hP := chenSiftingProduct_squarefree N z
  have hprime (q : ℕ) (hq : q ∈ P.primeFactors) : q < D := by
    change q ∈ (chenSiftingProduct N z).primeFactors at hq
    rw [chenSiftingProduct_primeFactors] at hq
    exact (chenSiftingPrime_lt_cutoff hq).trans_le hzD
  have hrem :
      linearSieveRemainder P D (chenA N) (chenA N).card chenDivisorDensity ≤
        chenReducedError N D (chenPrimeAPError N) := by
    unfold linearSieveRemainder chenReducedError chenPrimeAPError
    simp only [chenAPError, chenDivisible, chenDivisorDensity, mul_one_div]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro d hd
      obtain ⟨hdiv, hdD⟩ := Finset.mem_filter.mp hd
      have hdP := Nat.dvd_of_mem_divisors hdiv
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr ⟨Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero hP.ne_zero), hdD⟩,
          (chenSiftingProduct_coprime N z).of_dvd_left hdP⟩
    · intro d _ _
      exact abs_nonneg _
  have hfilter : (chenA N).filter (·.Coprime P) = chenSifted N z (chenA N) := by
    ext m
    simp only [chenSifted, Finset.mem_filter, chenRough_iff_coprime_product, P]
  have hbound := (linearSieveBounds hP hD hprime (chenA N) (chenA N).card chenDivisorDensity).1
  rw [hfilter] at hbound
  exact (sub_le_sub_left hrem _).trans hbound

private theorem roughThree_normalized_density_tendsto {a : ℝ} (ha : 0 < a) (ha₁ : a ≤ 1) :
    Tendsto (fun N : ℕ ↦ chenDensityProduct N (chenPowerLevel a N) * Real.log (N:ℝ) /
      chenCanonicalU N) chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / a)) := by
  have hV : Tendsto (chenLocalNormalized chenCanonicalU a) chenEvenAtTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    apply eventually_inf_principal.mpr
    filter_upwards [chenDensityProduct_cutoff_normalized ha ha₁ (δ/2) (by positivity)]
      with N hN he
    rw [Real.dist_eq, chenLocalNormalized, mul_comm (chenDensityProduct _ _)]
    exact (hN he).trans_lt (half_lt_self hδ)
  have h := hV.div ((chenLogPowerLevel_tendsto ha).mono_left inf_le_left) ha.ne'
  apply h.congr'
  have hlarge : chenEvenAtTop ≤ atTop := inf_le_left
  have hz := ((chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop (2:ℕ)).filter_mono hlarge
  filter_upwards [hz, (eventually_ge_atTop (2:ℕ)).filter_mono hlarge,
    chenCanonicalU_eventually_ge_half] with N hz hN hU
  have hN' : (1:ℝ) < N := Nat.one_lt_cast.mpr hN
  have hz' : (1:ℝ) < chenPowerLevel a N := Nat.one_lt_cast.mpr hz
  have hU' : 0 < chenCanonicalU N := by linarith
  have hlog := Real.log_pos hN'
  have hlogz := Real.log_pos hz'
  change (chenDensityProduct N (chenPowerLevel a N) * Real.log (chenPowerLevel a N:ℝ) /
      chenCanonicalU N) / (Real.log (chenPowerLevel a N:ℝ) / Real.log (N:ℝ)) = _
  field_simp [hU'.ne', hlog.ne', hlogz.ne']

private theorem roughThree_main_coefficient {ε : ℝ} (hε : 0 < ε) (hε₀ : ε < (1:ℝ)/524288) :
    let a : ℝ := 1/4 - ε
    let β : ℝ := 1/2 - ε/2
    (12:ℝ) * ε ≤
      (Real.exp (-Real.eulerMascheroniConstant) / a) * linearSieveLowerFactor (β/a) := by
  let a : ℝ := 1/4 - ε
  let β : ℝ := 1/2 - ε/2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha' : a ≤ 1/4 := by dsimp [a]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβ' : β ≤ 1/2 := by dsimp [β]; linarith
  let t := β/a - 2
  have ht : 0 < t := by
    apply sub_pos.mpr ((lt_div_iff₀ ha).mpr ?_)
    dsimp [a, β]
    linarith
  have ht₁ : t < 1 := by
    change β/a - 2 < 1
    have h := (div_lt_iff₀ ha).mpr (show β < 3 * a by dsimp [a, β]; linarith)
    linarith
  have htEq : a * t = 3*ε/2 := by
    dsimp only [t]
    field_simp [ha.ne']
    dsimp [a, β]
    ring
  have htLower : 6*ε ≤ t := by
    linarith only [htEq, mul_le_mul_of_nonneg_right ha' ht.le]
  have hlog : t/2 ≤ Real.log (1+t) := by
    apply le_trans _ (Real.le_log_one_add_of_nonneg ht.le)
    apply (le_div_iff₀ (show 0 < t+2 by linarith)).2
    nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr ht₁.le), ht.le]
  have harg : β/a - 1 = 1 + t := by dsimp [t]; ring
  change 12 * ε ≤ (Real.exp (-Real.eulerMascheroniConstant) / a) *
    linearSieveLowerFactor (β/a)
  have hcoefficient : (Real.exp (-Real.eulerMascheroniConstant) / a) *
      linearSieveLowerFactor (β/a) = 2 * Real.log (β/a - 1) / β := by
    rw [linearSieveLowerFactor, Real.exp_neg]
    field_simp [ha.ne', hβ.ne', Real.exp_ne_zero]
  rw [hcoefficient, harg]
  apply (le_div_iff₀ hβ).2
  linarith only [hlog, htLower, mul_le_mul_of_nonneg_left hβ' (show 0 ≤ 12*ε by positivity)]

/-- The normalized lower sieve has a positive margin just below a quarter power. -/
theorem chen_rough_three_clean_count_lower {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop, Even N →
      4*ε * chenSieveScale chenCanonicalU N ≤
        ((chenRoughThreeClean N (chenPowerLevel (1/4-ε) N)
          (chenPowerLevel (1/512) N + 1)).card : ℝ) := by
  let a : ℝ := 1/4 - ε
  let β : ℝ := 1/2 - ε/2
  let z := chenPowerLevel a
  let D := chenPowerLevel β
  let y (N : ℕ) := chenPowerLevel (1/512) N + 1
  let s (N : ℕ) := chenSieveParameter (D N) (z N)
  have ha : 0 < a := by dsimp [a]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβ₁ : 11/24 < β := by dsimp [β]; linarith
  have hβ₂ : β < 1/2 := by dsimp [β]; linarith
  have hs₂ : 2 < β/a := (lt_div_iff₀ ha).mpr (by dsimp [a, β]; linarith)
  have hs₄ : β/a < 4 := (div_lt_iff₀ ha).mpr (by dsimp [a, β]; linarith)
  have hlarge : chenEvenAtTop ≤ atTop := inf_le_left
  obtain ⟨K, hK, hlocal⟩ := chenBoundingSieve_dimension_one
  obtain ⟨C, _, hRos⟩ := rosser_first_interval_uniform K hK
  let E (N : ℕ) := C * (Real.log (D N : ℝ))^(-(1/2:ℝ))
  have hD : Tendsto D chenEvenAtTop atTop := (chenPowerLevel_tendsto_atTop hβ).mono_left hlarge
  have hz : Tendsto z chenEvenAtTop atTop := (chenPowerLevel_tendsto_atTop ha).mono_left hlarge
  have hs : Tendsto s chenEvenAtTop (𝓝 (β/a)) :=
    (chenSieveParameter_tendsto hβ ha).mono_left hlarge
  have hinterval := hs.eventually (Ioo_mem_nhds hs₂ hs₄)
  have hE : Tendsto E chenEvenAtTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/2)).comp
      (Real.tendsto_log_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)).comp hD))
    simpa only [E, Function.comp_apply, mul_zero] using h.const_mul C
  have hcont : ContinuousAt linearSieveLowerFactor (β/a) := by
    unfold linearSieveLowerFactor
    fun_prop (disch := intro H; linarith)
  have hF := hcont.tendsto.comp hs
  have hV := roughThree_normalized_density_tendsto ha (by dsimp [a]; linarith)
  obtain ⟨hpnt, hBV⟩ := chenPrimeAPDistribution_unconditional β hβ₁ hβ₂
  have hprod := ((hpnt.mono_left hlarge).mul hV).mul (hF.sub hE)
  simp only [one_mul, sub_zero] at hprod
  have hcoeff := roughThree_main_coefficient hε hε₀
  change 12*ε ≤ (Real.exp (-Real.eulerMascheroniConstant)/a) *
    linearSieveLowerFactor (β/a) at hcoeff
  have hmain := hprod.eventually (Ioi_mem_nhds (show 8*ε < _ from lt_of_lt_of_le
    (by linarith : 8*ε < 12*ε) hcoeff))
  have hySmall := eventually_rpow_add_one_le_powerLevel
    (a:=1/512) (b:=1/3) (by norm_num) (by norm_num)
  filter_upwards [(eventually_inf_principal.mp hmain), (eventually_inf_principal.mp hinterval),
    eventually_inf_principal.mp (hD.eventually hRos),
    eventually_inf_principal.mp (hD.eventually_ge_atTop (2:ℕ)),
    eventually_inf_principal.mp (hz.eventually_ge_atTop (2:ℕ)), hBV ε hε,
    chen_power_error_eventually_le ε hε, hySmall, eventually_ge_atTop (2^24:ℕ)]
    with N hmain hinterval hRos hD₂ hz₂ hBV hpower hySmall hN he
  have hN₂ : 2 ≤ N := by omega
  have hN₁ : (1:ℝ) ≤ N := Nat.one_le_cast.mpr (by omega)
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN₂)
  have hU := chenCanonicalU_ge_half he hN₂
  have hU' : 0 < chenCanonicalU N := by linarith
  have hzD : z N ≤ D N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le hN₁ (by dsimp [a, β]; linarith))
  have hzLarge : chenLowerCutoff N ≤ z N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le hN₁ (by dsimp [a]; linarith))
  have hyCut : y N ≤ chenUpperCutoff N := by
    have hfloor : (chenPowerLevel (1/512) N : ℝ) ≤ (N:ℝ)^(1/512:ℝ) :=
      Nat.floor_le (by positivity)
    change (N:ℝ)^(1/512:ℝ) + 1 ≤ (chenUpperCutoff N:ℝ) at hySmall
    have hreal : (chenPowerLevel (1/512) N : ℝ) + 1 ≤ (chenUpperCutoff N:ℝ) :=
      le_trans (by linarith only [hfloor]) hySmall
    change chenPowerLevel (1/512) N + 1 ≤ chenUpperCutoff N
    exact_mod_cast hreal
  let S := chenBoundingSieve he (z N)
  have hcut (q : ℕ) (hq : q ∈ S.prodPrimes.primeFactors) :
      q < ⌈(D N:ℝ)^(1/s N)⌉₊ := by
    rw [show ⌈(D N:ℝ)^(1/s N)⌉₊ = z N from chenSieveParameter_cutoff (hD₂ he) (hz₂ he)]
    apply chenSiftingPrime_lt_cutoff (N:=N)
    simpa only [S, chenBoundingSieve_prodPrimes, chenSiftingProduct_primeFactors] using hq
  have hVeq : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S = chenDensityProduct N (z N) := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors chenDensityProduct
    simp only [S, chenBoundingSieve_prodPrimes, chenSiftingProduct_primeFactors,
      chenBoundingSieve_nu, chenDivisorDensity]
  obtain ⟨hsLo, hsHi⟩ := hinterval he
  have hcomparison :
      chenDensityProduct N (z N) * (linearSieveLowerFactor (s N) - E N) ≤
        linearSieveMain false (chenSiftingProduct N (z N)) (D N) chenDivisorDensity := by
    have h := ((hRos he) S (s N) (hlocal N (z N) he) hcut).2 hsLo.le hsHi.le
    have hν : (S.nu : ℕ → ℝ) = chenDivisorDensity := rfl
    simpa only [hVeq, hν, S, chenBoundingSieve_prodPrimes, E] using h
  let T := chenSieveScale chenCanonicalU N
  have hT : 0 ≤ T := by dsimp [T, chenSieveScale]; positivity
  have hterm : 8*ε * T ≤ ((chenA N).card:ℝ) *
      (chenDensityProduct N (z N) * (linearSieveLowerFactor (s N) - E N)) := by
    have hm := mul_le_mul_of_nonneg_right (hmain he).le hT
    refine hm.trans_eq ?_
    change (((chenA N).card:ℝ)/((N:ℝ)/Real.log (N:ℝ)) *
        (chenDensityProduct N (z N)*Real.log (N:ℝ)/chenCanonicalU N) *
        (linearSieveLowerFactor (s N) - E N)) * T = _
    dsimp only [T, chenSieveScale]
    have hNpos : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
    field_simp [hlog.ne', hU'.ne', hNpos.ne']
  have hmainBound := hterm.trans (mul_le_mul_of_nonneg_left hcomparison (Nat.cast_nonneg _))
  have hlogScale : chenLogScale N ≤ 2*T := by
    unfold chenLogScale T chenSieveScale
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg (α:=ℝ) N)]
  have hrem : chenReducedError N (D N) (chenPrimeAPError N) ≤ 2*ε*T := by
    calc
      _ ≤ ε * chenLogScale N := (hBV he).1
      _ ≤ ε * (2*T) := mul_le_mul_of_nonneg_left hlogScale hε.le
      _ = _ := by ring
  have hsift := roughThree_finite_lower (N:=N) hzD (show 1 < D N from hD₂ he)
  have hbad := (roughThree_bad_card_le_eighth hzLarge hyCut).trans
    ((chenElementaryError_le hN).trans (hpower chenCanonicalU hU))
  have hsub : chenBadSet N (z N) (y N) ⊆ chenSifted N (z N) (chenA N) :=
    fun _ hm ↦ (Finset.mem_filter.mp hm).1
  have hcard : ((chenRoughThreeClean N (z N) (y N)).card:ℝ) +
      ((chenBadSet N (z N) (y N)).card:ℝ) = ((chenSifted N (z N) (chenA N)).card:ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  change 4*ε*T ≤ ((chenRoughThreeClean N (z N) (y N)).card:ℝ)
  linarith only [hmainBound, hrem, hsift, hbad, hcard, mul_nonneg hε.le hT]

end FareyGoldbach
