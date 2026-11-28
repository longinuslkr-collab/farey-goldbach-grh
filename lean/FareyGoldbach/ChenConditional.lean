import FareyGoldbach.LinearSieve
import FareyGoldbach.ChenConditionalMargin
import FareyGoldbach.ChenSieveLevel

/-! # From Rosser main-polynomial comparisons to Chen's count

The analytic comparison of the Rosser polynomials is an explicit input. The
distribution premises concern only unsifted progressions and carrier sizes.
-/

open Filter MeasureTheory Set
open scoped Topology Classical

namespace FareyGoldbach

noncomputable def chenDivisorDensity (d : ℕ) : ℝ := 1/(d.totient:ℝ)

noncomputable def chenLowerPolynomial (θ : ℝ) (N : ℕ) : ℝ :=
  linearSieveMain false (chenSiftingProduct N (chenLowerCutoff N))
    (chenPowerLevel θ N) chenDivisorDensity

noncomputable def chenMediumPolynomial (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    if q∣N then 0 else chenDivisorDensity q *
      linearSieveMain true (chenSiftingProduct N (chenLowerCutoff N))
        (chenPowerLevel θ N/q) chenDivisorDensity

noncomputable def chenSwitchedPolynomial (θ : ℝ) (N : ℕ) : ℝ :=
  linearSieveMain true (chenSiftingProduct N (chenUpperCutoff N))
    (chenPowerLevel θ N) chenDivisorDensity

/-- The normalized main-polynomial comparisons needed at a single exponent.
The switched comparison is for the polynomial, before its carrier cardinality
enters. The medium comparison incorporates just the reciprocal-totient weights. -/
def ChenRosserMainComparisons (θ : ℝ) (U : ℕ→ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N →
    (chenLowerMainCoeff θ-ε)*(U N/Real.log (N:ℝ))≤chenLowerPolynomial θ N ∧
    chenMediumPolynomial θ N≤(chenMediumMainCoeff θ+ε)*(U N/Real.log (N:ℝ)) ∧
    chenSwitchedPolynomial θ N≤(2/θ+ε)*(U N/Real.log (N:ℝ))

private theorem chenRemainder_eq_sum {N z D : ℕ} (A : Finset ℕ) (X : ℝ) :
    linearSieveRemainder (chenSiftingProduct N z) D A X chenDivisorDensity =
      ∑ d ∈ (Finset.Ico 1 D).filter (fun d => d∣chenSiftingProduct N z), |chenAPError A X d| := by
  unfold linearSieveRemainder
  have hs : (chenSiftingProduct N z).divisors.filter (fun d => d<D) =
      (Finset.Ico 1 D).filter (fun d => d∣chenSiftingProduct N z) := by
    ext d
    have h0 := (chenSiftingProduct_squarefree N z).ne_zero
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Ico]
    constructor
    · rintro ⟨hd,hD⟩
      have hp := Nat.pos_of_dvd_of_pos hd.1 (Nat.pos_of_ne_zero h0)
      exact ⟨⟨hp,hD⟩,hd.1⟩
    · rintro ⟨⟨_,hd⟩,hdiv⟩
      exact ⟨⟨hdiv,h0⟩,hd⟩
  rw [hs]
  simp only [chenAPError,chenDivisible,chenDivisorDensity,mul_one_div]

private theorem chenRemainder_le_reduced (N z D : ℕ) (A : Finset ℕ) (X : ℝ) :
    linearSieveRemainder (chenSiftingProduct N z) D A X chenDivisorDensity ≤
      chenReducedError N D (chenAPError A X) := by
  rw [chenRemainder_eq_sum,chenReducedError]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdh,hdd⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hdh,(chenSiftingProduct_coprime N z).of_dvd_left hdd⟩
  · intro d _ _
    exact abs_nonneg _

noncomputable def chenCarrierMediumMass (K : ℕ) (A : Finset ℕ) (q : ℕ) : ℝ :=
  if q∣K then 0 else (A.card:ℝ)/(q.totient:ℝ)

noncomputable def chenCarrierMediumError (K z y D : ℕ) (A : Finset ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes z y,
    ∑ d∈(Finset.Ico 1 (D/q)).filter (fun d => d∣chenSiftingProduct K z),
      |chenAPError (chenDivisible A q) (chenCarrierMediumMass K A q) d|

/-- The finite sieve bounds depend on the two carriers and on the integer
whose prime divisors are omitted. The cutoffs still use the size N. -/
theorem chen_finite_sieve_terms_for_carriers {θ : ℝ} (hθ : 11/24 < θ)
    {N : ℕ} (hN : 2^24≤N) (K : ℕ) (A B : Finset ℕ) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    let D := chenPowerLevel θ N
    let P := chenSiftingProduct K z
    let P' := chenSiftingProduct K y
    (A.card:ℝ)*linearSieveMain false P D chenDivisorDensity -
      chenReducedError K D (chenAPError A A.card) ≤ ((chenSifted K z A).card:ℝ) ∧
    (∑ q∈chenMediumPrimes z y, ((chenSifted K z (chenDivisible A q)).card:ℝ)) ≤
      (A.card:ℝ)*(∑ q∈chenMediumPrimes z y,
        if q∣K then 0 else chenDivisorDensity q*linearSieveMain true P (D/q) chenDivisorDensity) +
      chenCarrierMediumError K z y D A ∧
    ((chenSifted K y B).card:ℝ) ≤
      (B.card:ℝ)*linearSieveMain true P' D chenDivisorDensity +
      chenReducedError K D (chenAPError B B.card) := by
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let D := chenPowerLevel θ N
  let P := chenSiftingProduct K z
  let P' := chenSiftingProduct K y
  have ⟨hz,hy,hzy⟩ : 2≤z ∧ 2≤y ∧ z*y≤D := chenPowerLevel_cutoffs hθ hN
  have hzD : z≤D := (Nat.le_mul_of_pos_right z (by omega)).trans hzy
  have hyD : y≤D := (Nat.le_mul_of_pos_left y (by omega)).trans hzy
  have hP (p : ℕ) (hp : p∈P.primeFactors) : p<z := by
    rw [show P.primeFactors=chenSiftingPrimes K z from chenSiftingProduct_primeFactors K z] at hp
    exact Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hP' (p : ℕ) (hp : p∈P'.primeFactors) : p<y := by
    rw [show P'.primeFactors=chenSiftingPrimes K y from chenSiftingProduct_primeFactors K y] at hp
    exact Finset.mem_range.mp (Finset.mem_filter.mp hp).1
  have hfilter (w : ℕ) (C : Finset ℕ) :
      C.filter (fun n => n.Coprime (chenSiftingProduct K w)) = chenSifted K w C := by
    ext n
    simp only [chenSifted,Finset.mem_filter,chenRough_iff_coprime_product]
  have h₁ := (linearSieveBounds (chenSiftingProduct_squarefree K z) (show 1<D by omega)
    (fun p hp => (hP p hp).trans_le hzD) A A.card chenDivisorDensity).1
  have h₃ := (linearSieveBounds (chenSiftingProduct_squarefree K y) (show 1<D by omega)
    (fun p hp => (hP' p hp).trans_le hyD) B B.card chenDivisorDensity).2
  rw [hfilter] at h₁ h₃
  refine ⟨(sub_le_sub_left (chenRemainder_le_reduced K z D A A.card) _).trans h₁,?_,
    h₃.trans (add_le_add_right (chenRemainder_le_reduced K y D B B.card) _)⟩
  let Q := chenMediumPrimes z y
  let W (q : ℕ) := linearSieveMain true P (D/q) chenDivisorDensity
  let E (q : ℕ) := linearSieveRemainder P (D/q) (chenDivisible A q) (chenCarrierMediumMass K A q)
    chenDivisorDensity
  have hw (q : ℕ) (hq : q∈Q) :
      ((chenSifted K z (chenDivisible A q)).card:ℝ) ≤ chenCarrierMediumMass K A q*W q+E q := by
    obtain ⟨hqI,hqP⟩ := Finset.mem_filter.mp hq
    have hzq : z≤D/q := (Nat.le_div_iff_mul_le hqP.pos).2
      ((Nat.mul_le_mul_left z (Finset.mem_Ico.mp hqI).2.le).trans hzy)
    have hb := (linearSieveBounds (chenSiftingProduct_squarefree K z) (show 1<D/q by omega)
      (fun p hp => (hP p hp).trans_le hzq) (chenDivisible A q) (chenCarrierMediumMass K A q)
        chenDivisorDensity).2
    rwa [hfilter] at hb
  have hM : (∑ q∈Q,chenCarrierMediumMass K A q*W q) =
      (A.card:ℝ)*(∑ q∈Q, if q∣K then 0 else chenDivisorDensity q*W q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q∣K
    · simp [chenCarrierMediumMass,hq]
    · simp only [chenCarrierMediumMass,hq,ite_false,chenDivisorDensity]
      ring
  have hE : (∑ q∈Q, E q) = chenCarrierMediumError K z y D A := by
    unfold chenCarrierMediumError
    apply Finset.sum_congr rfl
    intro q _
    exact chenRemainder_eq_sum ..
  change (∑ q∈Q, ((chenSifted K z (chenDivisible A q)).card:ℝ)) ≤ _
  calc _ ≤ ∑ q∈Q, (chenCarrierMediumMass K A q*W q+E q) := Finset.sum_le_sum hw
       _ = _ := by rw [Finset.sum_add_distrib,hM,hE]

private theorem chen_finite_sieve_terms {θ : ℝ} (hθ : 11/24 < θ) {N : ℕ} (hN : 2^24≤N) :
    ((chenA N).card:ℝ)*chenLowerPolynomial θ N -
      chenReducedError N (chenPowerLevel θ N) (chenPrimeAPError N) ≤ chenFloorLowerTerm N ∧
    chenFloorMediumTerm N ≤ ((chenA N).card:ℝ)*chenMediumPolynomial θ N +
      chenMediumError N (chenPowerLevel θ N) ∧
    chenFloorSwitchedTerm N ≤
      ((chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card:ℝ)*chenSwitchedPolynomial θ N +
      chenReducedError N (chenPowerLevel θ N) (chenSwitchingAPError N) :=
  chen_finite_sieve_terms_for_carriers hθ hN N (chenA N)
    (chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N))

theorem chen_coeff_pos {θ : ℝ} (hθ : 11/24<θ) :
    0<chenLowerMainCoeff θ ∧ 0≤chenMediumMainCoeff θ ∧ 0<2/θ := by
  have hθp : 0<θ := by linarith
  have h₃ : 0<3*θ-1 := by linarith
  have h₈ : 1<8*θ-1 := by linarith
  refine ⟨?_,?_,div_pos (by norm_num) hθp⟩
  · exact mul_pos (div_pos (by norm_num) hθp) (Real.log_pos h₈)
  · apply mul_nonneg (div_nonneg (by norm_num) hθp.le)
    apply Real.log_nonneg
    exact (one_le_div h₃).2 (by linarith)

theorem chenSwitchIntegral_nonneg : 0≤chenSwitchIntegral := by
  unfold chenSwitchIntegral
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro t ht
  exact div_nonneg (Real.log_nonneg (by linarith [ht.2]))
    (mul_nonneg (by linarith [ht.1]) (by linarith [ht.2]))

theorem chen_profile_budget {a m b c ε : ℝ} (ha : 0<a) (hm : 0≤m)
    (hb : 0≤b) (hc : 0≤c) (hε : 0<ε) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ δ≤a ∧
      a-ε≤(1-δ)*(a-δ)-2*δ ∧
      (1+δ)*(m+δ)+2*δ≤m+ε ∧
      (c+δ)*(b+δ)+2*δ≤c*b+ε := by
  let C := a+m+b+c+8
  have hC : 0<C := by dsimp [C]; linarith
  let δ := min a (min 1 (ε/C))
  have hd : 0<δ := lt_min ha (lt_min zero_lt_one (div_pos hε hC))
  have hda : δ≤a := min_le_left ..
  have hd₁ : δ≤1 := (min_le_right ..).trans (min_le_left ..)
  have hdc : δ*C≤ε := (le_div_iff₀ hC).1 ((min_le_right ..).trans (min_le_right ..))
  have hd' := mul_le_mul_of_nonneg_left hd₁ hd.le
  have hl := mul_le_mul_of_nonneg_left (show a+3≤C by dsimp [C]; linarith) hd.le
  have hm' := mul_le_mul_of_nonneg_left (show m+4≤C by dsimp [C]; linarith) hd.le
  have hb' := mul_le_mul_of_nonneg_left (show c+b+3≤C by dsimp [C]; linarith) hd.le
  exact ⟨δ,hd,hd₁,hda,by nlinarith only [hl,hdc,sq_nonneg δ],
    by nlinarith only [hm',hdc,hd'],by nlinarith only [hb',hdc,hd']⟩

/-- The unsifted arithmetic distributions and the normalized analytic Rosser
comparisons imply the required three sieve estimates at a fixed level. -/
theorem chenSieveTerms_of_distributions_and_comparisons {θ : ℝ} (hθ : 11/24<θ)
    (U : ℕ→ℝ) (hU : ∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N)
    (hA : ChenPrimeAPDistributionAt (chenPowerLevel θ))
    (hB : ChenSwitchingDistributionAt (chenPowerLevel θ))
    (hM : ChenRosserMainComparisons θ U) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (chenLowerMainCoeff θ-ε)*chenSieveScale U N ≤ chenFloorLowerTerm N ∧
      chenFloorMediumTerm N ≤ (chenMediumMainCoeff θ+ε)*chenSieveScale U N ∧
      chenFloorSwitchedTerm N ≤ (chenSwitchedMainCoeff θ+ε)*chenSieveScale U N := by
  let a := chenLowerMainCoeff θ
  let m := chenMediumMainCoeff θ
  let b := 2/θ
  let c := chenSwitchIntegral
  have ⟨ha,hm,hb⟩ : 0<a ∧ 0≤m ∧ 0<b := chen_coeff_pos hθ
  have hc : 0≤c := chenSwitchIntegral_nonneg
  obtain ⟨δ,hd,hd₁,hda,hbud₁,hbud₂,hbud₃⟩ := chen_profile_budget ha hm hb.le hc hε
  obtain ⟨hπ,hApr⟩ := hA
  obtain ⟨hBmass,hBpr⟩ := hB
  have hπlo := hπ.eventually (Ioi_mem_nhds (show (1:ℝ)-δ<1 by linarith))
  have hπhi := hπ.eventually_lt_const (show (1:ℝ)<1+δ by linarith)
  filter_upwards [eventually_ge_atTop (2^24:ℕ),hU,hπlo,hπhi,hApr δ hd,
    hBmass δ hd,hBpr δ hd,hM δ hd] with N hN hU hπlo hπhi hApr hBs hBpr hProfile hEven
  let R := (N:ℝ)/Real.log (N:ℝ)
  let v := U N/Real.log (N:ℝ)
  let T := chenSieveScale U N
  let A := (chenA N).card
  let B := (chenUnrestrictedB N (chenLowerCutoff N) (chenUpperCutoff N)).card
  have hN' : (2:ℝ)≤N := by exact_mod_cast (show (2:ℕ)≤N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hR : 0<R := by dsimp [R]; positivity
  have hU' := hU hEven
  have hv : 0≤v := by dsimp [v]; positivity
  have hT : T=R*v := by dsimp only [T,R,v,chenSieveScale]; ring
  have hT₀ : 0≤T := hT.symm ▸ mul_nonneg hR.le hv
  have hlog : chenLogScale N≤2*T := by
    unfold chenLogScale T chenSieveScale
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hU' (Nat.cast_nonneg (α:=ℝ) N)]
  have hErr := mul_le_mul_of_nonneg_left hlog hd.le
  have hAl : (1-δ)*R≤(A:ℝ) := ((lt_div_iff₀ hR).1 hπlo).le
  have hAu : (A:ℝ)≤(1+δ)*R := ((div_lt_iff₀ hR).1 hπhi).le
  have hBu : (B:ℝ)≤(c+δ)*R := hBs hEven
  obtain ⟨hFin₁,hFin₂,hFin₃⟩ := chen_finite_sieve_terms hθ hN
  obtain ⟨hP₁,hP₂,hP₃⟩ := hProfile hEven
  obtain ⟨he₁,he₂⟩ := hApr hEven
  have he₃ := hBpr hEven
  have hLow : ((1-δ)*(a-δ))*T ≤ (A:ℝ)*chenLowerPolynomial θ N := by
    calc _ = ((1-δ)*R)*((a-δ)*v) := by rw [hT]; ring
         _ ≤ (A:ℝ)*((a-δ)*v) := mul_le_mul_of_nonneg_right hAl
           (mul_nonneg (sub_nonneg.mpr hda) hv)
         _ ≤ _ := mul_le_mul_of_nonneg_left hP₁ (Nat.cast_nonneg _)
  have hMed : (A:ℝ)*chenMediumPolynomial θ N ≤ ((1+δ)*(m+δ))*T := by
    calc _ ≤ (A:ℝ)*((m+δ)*v) := mul_le_mul_of_nonneg_left hP₂ (Nat.cast_nonneg _)
         _ ≤ ((1+δ)*R)*((m+δ)*v) := mul_le_mul_of_nonneg_right hAu (by positivity)
         _ = _ := by rw [hT]; ring
  have hSwi : (B:ℝ)*chenSwitchedPolynomial θ N ≤ ((c+δ)*(b+δ))*T := by
    calc _ ≤ (B:ℝ)*((b+δ)*v) := mul_le_mul_of_nonneg_left hP₃ (Nat.cast_nonneg _)
         _ ≤ ((c+δ)*R)*((b+δ)*v) := mul_le_mul_of_nonneg_right hBu (by positivity)
         _ = _ := by rw [hT]; ring
  have h₁ := mul_le_mul_of_nonneg_right hbud₁ hT₀
  have h₂ := mul_le_mul_of_nonneg_right hbud₂ hT₀
  have h₃ := mul_le_mul_of_nonneg_right hbud₃ hT₀
  change (a-ε)*T≤chenFloorLowerTerm N ∧ chenFloorMediumTerm N≤(m+ε)*T ∧
    chenFloorSwitchedTerm N≤(b*c+ε)*T
  exact ⟨by linarith only [h₁,hLow,hFin₁,he₁,hErr],
    by linarith only [h₂,hMed,hFin₂,he₂,hErr],
    by linarith only [h₃,hSwi,hFin₃,he₃,hErr]⟩

/-- Quantitative conditional assembly for rough Chen representations. The analytic polynomial comparisons
and the two arithmetic distribution interfaces are needed. -/
theorem chen_rough_count_lower_of_distributions_and_comparisons
    (hA : ChenPrimeAPDistribution) (hB : ChenSwitchingDistribution)
    (hMain : ∀ θ : ℝ, 11/24<θ → θ<1/2 → ∃ U : ℕ→ℝ,
      (∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N) ∧ ChenRosserMainComparisons θ U) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤
        ((chenRoughRepresentations N (chenLowerCutoff N)).card:ℝ) := by
  obtain ⟨θ,hθ,hm⟩ := chen_margin_near_half
  have hθlo := hθ.1
  have hθhi := hθ.2
  obtain ⟨U,hU,hM⟩ := hMain θ hθlo hθhi
  refine ⟨1/100,by norm_num,chen_rough_count_lower_of_sieve_terms U (hm θ ⟨le_rfl,hθhi.le⟩) hU ?_⟩
  exact fun ε hε => chenSieveTerms_of_distributions_and_comparisons hθlo U hU
    (hA θ hθlo hθhi) (hB θ hθlo hθhi) hM hε

/-- Quantitative conditional assembly. Only the analytic polynomial comparisons
and the two arithmetic distribution interfaces are needed. -/
theorem chen_count_lower_of_distributions_and_comparisons
    (hA : ChenPrimeAPDistribution) (hB : ChenSwitchingDistribution)
    (hMain : ∀ θ : ℝ, 11/24<θ → θ<1/2 → ∃ U : ℕ→ℝ,
      (∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N) ∧ ChenRosserMainComparisons θ U) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2 ≤ (chenCount N:ℝ) := by
  obtain ⟨c, hc, hcount⟩ := chen_rough_count_lower_of_distributions_and_comparisons hA hB hMain
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcount] with N hN hEven
  exact (hN hEven).trans (Nat.cast_le.mpr (chenRoughRepresentations_card_le_chenCount N (chenLowerCutoff N)))

/-- Chen's representation with the two arithmetic distributions and the
explicit analytic main-polynomial input. -/
theorem chen_theorem_of_distributions_and_comparisons
    (hA : ChenPrimeAPDistribution) (hB : ChenSwitchingDistribution)
    (hMain : ∀ θ : ℝ, 11/24<θ → θ<1/2 → ∃ U : ℕ→ℝ,
      (∀ᶠ N : ℕ in atTop, Even N → (1:ℝ)/2≤U N) ∧ ChenRosserMainComparisons θ U) :
    ∀ᶠ N : ℕ in atTop, Even N → ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N := by
  obtain ⟨c,hc,hcN⟩ := chen_count_lower_of_distributions_and_comparisons hA hB hMain
  filter_upwards [hcN,eventually_ge_atTop (2:ℕ)] with N hh hN he
  have hN' : (2:ℝ)≤N := Nat.cast_le.mpr hN
  have hl : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hp : (0:ℝ)<(chenCount N:ℝ) := (show 0<c*(N:ℝ)/Real.log (N:ℝ)^2 by positivity).trans_le
    (hh he)
  have hpos := Nat.cast_pos.mp hp
  rw [chenCount_eq_representations_card] at hpos
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hpos
  obtain ⟨hr,hp,hP⟩ := Finset.mem_filter.mp hp
  refine ⟨p,N-p,hp,hP,?_⟩
  have hle := Finset.mem_range.mp hr
  omega

end FareyGoldbach
