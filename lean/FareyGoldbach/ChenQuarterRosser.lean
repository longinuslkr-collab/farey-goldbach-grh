import FareyGoldbach.ChenTheoremUnconditional
import FareyGoldbach.ChenSwitchingScales

/-! # The base and conditioned Rosser estimates for the quarter-power switch -/

open Filter Set
open scoped Classical Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace FareyGoldbach

/-- Normalized lower-sieve coefficient at distribution exponent δ and lower cutoff a. -/
noncomputable def chenQuarterLowerCoeff (δ a : ℝ) : ℝ :=
  (2/δ)*Real.log (δ/a-1)

/-- The full middle-prime coefficient before applying its one-half weight. -/
noncomputable def chenQuarterMediumCoeff (δ a : ℝ) : ℝ :=
  (2/δ)*Real.log (((1/4)/(δ-1/4))/(a/(δ-a)))

private noncomputable def quarterMediumIdealSum (δ a : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N),
    if q ∣ N then 0 else chenDivisorDensity q * (2/(δ-Real.log (q:ℝ)/Real.log (N:ℝ)))

private noncomputable def quarterMediumPolynomial (δ a : ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N),
    if q ∣ N then 0 else chenDivisorDensity q *
      linearSieveMain true (chenSiftingProduct N (chenLowerCutoff N))
        (chenPowerLevel δ N/q) chenDivisorDensity

private theorem quarterMediumSubset {a : ℝ} (ha : 1/8 ≤ a) {N : ℕ} (hN : 1 ≤ N) :
    chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N) ⊆
      chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N) := by
  intro q hq
  obtain ⟨hI,hp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hI
  have hN' : (1:ℝ) ≤ N := Nat.one_le_cast.mpr hN
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
    ⟨(Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN' ha)).trans hlo,
      hhi.trans_le (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hN' (by norm_num)))⟩,hp⟩

private theorem quarterMediumCoeff_nonneg {θ a : ℝ} (hθ : 11/24 < θ)
    (ha : 1/8 ≤ a) (ha' : a ≤ 1/4) : 0 ≤ chenQuarterMediumCoeff θ a := by
  have hap : 0 < a := by linarith
  have h₁ : 0 < θ-a := by linarith
  have h₂ : 0 < θ-1/4 := by linarith
  have hq : a/(θ-a) ≤ (1/4:ℝ)/(θ-1/4) := (div_le_div_iff₀ h₁ h₂).2 (by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha') (show 0 ≤ θ by linarith)])
  unfold chenQuarterMediumCoeff
  exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div (div_pos hap h₁)).2 hq))

private theorem quarterRemainder_eq_sum {N z D : ℕ} (A : Finset ℕ) (X : ℝ) :
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

private theorem quarterRemainder_le_reduced (N z D : ℕ) (A : Finset ℕ) (X : ℝ) :
    linearSieveRemainder (chenSiftingProduct N z) D A X chenDivisorDensity ≤
      chenReducedError N D (chenAPError A X) := by
  rw [quarterRemainder_eq_sum,chenReducedError]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hdh,hdd⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hdh,(chenSiftingProduct_coprime N z).of_dvd_left hdd⟩
  · intro d _ _
    exact abs_nonneg _

private theorem quarterDensityProduct_nonneg (N w : ℕ) : 0≤chenDensityProduct N w := by
  unfold chenDensityProduct
  apply Finset.prod_nonneg
  intro p hp
  have h := (Finset.mem_filter.mp hp).2.1.pos
  have hφ : (1:ℝ)≤p.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr h)
  exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hφ)).2 hφ)

private theorem quarterEven_large (k : ℕ) : ∀ᶠ N in chenEvenAtTop, k≤N :=
  (eventually_ge_atTop k).filter_mono inf_le_left

private theorem quarterEven_log_pos : ∀ᶠ N : ℕ in chenEvenAtTop, 0<Real.log (N:ℝ) := by
  filter_upwards [quarterEven_large 2] with N hN
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  exact Real.log_pos (by linarith)

private theorem quarter_normalized_density_tendsto {U : ℕ→ℝ} {a : ℝ} (ha : 0<a)
    (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : Tendsto (chenLocalNormalized U a) chenEvenAtTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))) :
    Tendsto (fun N => chenDensityProduct N (chenPowerLevel a N)*Real.log (N:ℝ)/U N)
      chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/a)) := by
  have h := hV.div ((chenLogPowerLevel_tendsto ha).mono_left inf_le_left) ha.ne'
  apply h.congr'
  have hw := ((chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop (2:ℕ)).filter_mono
    (show chenEvenAtTop≤atTop from inf_le_left)
  filter_upwards [quarterEven_log_pos,hw,hU] with N hL hw hU'
  have hw' : (2:ℝ)≤chenPowerLevel a N := by exact_mod_cast hw
  have hlw : 0<Real.log (chenPowerLevel a N : ℝ) := Real.log_pos (by linarith)
  have hpos : 0<U N := by linarith
  change (chenDensityProduct N (chenPowerLevel a N)*Real.log (chenPowerLevel a N:ℝ)/U N)/
    (Real.log (chenPowerLevel a N:ℝ)/Real.log (N:ℝ)) = _
  field_simp


private theorem quarterLocalNormalization {a : ℝ} (ha : 0<a) (ha' : a≤1) :
    Tendsto (chenLocalNormalized chenCanonicalU a) chenEvenAtTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_inf_principal.mpr
  filter_upwards [chenDensityProduct_cutoff_normalized ha ha' (ε/2) (by positivity)]
    with N hN he
  rw [Real.dist_eq, chenLocalNormalized, mul_comm (chenDensityProduct _ _)]
  exact (hN he).trans_lt (half_lt_self hε)

private theorem quarterFixedRosser {δ a η : ℝ} (hδ : 0<δ) (ha : 0<a) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      let D := chenPowerLevel δ N
      let z := chenPowerLevel a N
      let s := chenSieveParameter D z
      (1<s → s≤3 → linearSieveMain true (chenSiftingProduct N z) D chenDivisorDensity ≤
        chenDensityProduct N z * (linearSieveUpperFactor s + η)) ∧
      (2≤s → s≤4 → chenDensityProduct N z * (linearSieveLowerFactor s - η) ≤
        linearSieveMain false (chenSiftingProduct N z) D chenDivisorDensity) := by
  obtain ⟨K,hK,hloc⟩ := chenBoundingSieve_dimension_one
  obtain ⟨C,_,hRos⟩ := rosser_first_interval_uniform K hK
  have hlimit : Tendsto (fun D : ℕ ↦ C*(Real.log (D:ℝ))^(-(1/2:ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
    simpa only [Function.comp_apply,mul_zero] using h.const_mul C
  have hD := chenPowerLevel_tendsto_atTop hδ
  filter_upwards [hD.eventually hRos, hD.eventually (hlimit.eventually_lt_const hη),
    hD.eventually_ge_atTop 2, (chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop 2]
    with N hRos hErr hD hz he
  let D := chenPowerLevel δ N
  let z := chenPowerLevel a N
  let s := chenSieveParameter D z
  let S := chenBoundingSieve he z
  have hcut (q : ℕ) (hq : q ∈ S.prodPrimes.primeFactors) : q < ⌈(D:ℝ)^(1/s)⌉₊ := by
    rw [show ⌈(D:ℝ)^(1/s)⌉₊ = z from chenSieveParameter_cutoff hD hz]
    apply chenSiftingPrime_lt_cutoff (N:=N)
    simpa only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors] using hq
  have hV : AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S = chenDensityProduct N z := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors chenDensityProduct
    simp only [S,chenBoundingSieve_prodPrimes,chenSiftingProduct_primeFactors,
      chenBoundingSieve_nu,chenDivisorDensity]
  have hν : (S.nu : ℕ→ℝ) = chenDivisorDensity := rfl
  have h := hRos S s (hloc N z he) hcut
  have hV₀ := quarterDensityProduct_nonneg N z
  change (1<s → s≤3 → _) ∧ (2≤s → s≤4 → _)
  constructor
  · intro hs₁ hs₃
    have hb := h.1 hs₁ hs₃
    rw [hV] at hb
    have hh := hb.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hErr.le) hV₀)
    simpa only [S,hν,chenBoundingSieve_prodPrimes] using hh
  · intro hs₂ hs₄
    have hb := h.2 hs₂ hs₄
    rw [hV] at hb
    have hh := (mul_le_mul_of_nonneg_left (sub_le_sub_left hErr.le _) hV₀).trans hb
    simpa only [S,hV,hν,chenBoundingSieve_prodPrimes] using hh

set_option maxHeartbeats 500000 in
private theorem quarterFiniteSieve {N z D : ℕ} (hzD : z≤D) (hD : 1<D) (A : Finset ℕ) :
    (A.card:ℝ) * linearSieveMain false (chenSiftingProduct N z) D chenDivisorDensity -
      chenReducedError N D (chenAPError A A.card) ≤ ((chenSifted N z A).card:ℝ) ∧
    ((chenSifted N z A).card:ℝ) ≤
      (A.card:ℝ) * linearSieveMain true (chenSiftingProduct N z) D chenDivisorDensity +
      chenReducedError N D (chenAPError A A.card) := by
  have hP := chenSiftingProduct_squarefree N z
  have hprime (q : ℕ) (hq : q∈(chenSiftingProduct N z).primeFactors) : q<D := by
    rw [chenSiftingProduct_primeFactors] at hq
    exact (chenSiftingPrime_lt_cutoff hq).trans_le hzD
  have hf : A.filter (·.Coprime (chenSiftingProduct N z)) = chenSifted N z A := by
    ext m
    simp only [chenSifted,Finset.mem_filter,chenRough_iff_coprime_product]
  have h := linearSieveBounds hP hD hprime A A.card chenDivisorDensity
  rw [hf] at h
  have hr := quarterRemainder_le_reduced N z D A A.card
  exact ⟨(sub_le_sub_left hr _).trans h.1,h.2.trans (add_le_add le_rfl hr)⟩

private theorem quarterMediumFinite {δ a : ℝ} (hδ : 11/24<δ) (ha : 1/8≤a)
    {N : ℕ} (hN : 2^24≤N) :
    (∑ q ∈ chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N),
      ((chenSifted N (chenPowerLevel a N) (chenDivisible (chenA N) q)).card:ℝ)) ≤
      ((chenA N).card:ℝ)*quarterMediumPolynomial δ a N + chenMediumError N (chenPowerLevel δ N) := by
  let Q := chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N)
  let z := chenLowerCutoff N
  let D := chenPowerLevel δ N
  let P := chenSiftingProduct N z
  let W (q : ℕ) := linearSieveMain true P (D/q) chenDivisorDensity
  let E (q : ℕ) := linearSieveRemainder P (D/q) (chenDivisible (chenA N) q) (chenMediumMass N q)
    chenDivisorDensity
  have hQ := quarterMediumSubset ha (by omega : 1≤N)
  have hz : 2≤z := (chenPowerLevel_cutoffs hδ hN).1
  have hzle : z ≤ chenPowerLevel a N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega)) ha)
  have hs (q : ℕ) : chenSifted N (chenPowerLevel a N) (chenDivisible (chenA N) q) ⊆
      chenSifted N z (chenDivisible (chenA N) q) := by
    intro m hm
    obtain ⟨hm,hr⟩ := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr ⟨hm,fun p hp ↦
      hr p (Finset.mem_range.mpr ((Finset.mem_range.mp hp).trans_le hzle))⟩
  have hM (q : ℕ) (hq : q∈Q) :
      ((chenSifted N (chenPowerLevel a N) (chenDivisible (chenA N) q)).card:ℝ) ≤
      chenMediumMass N q*W q + E q := by
    have hqD : z≤D/q := chen_mediumNat_div_ge_lower hδ hN (hQ hq)
    have hp (p : ℕ) (hp : p∈P.primeFactors) : p<D/q := by
      rw [show P.primeFactors = chenSiftingPrimes N z from chenSiftingProduct_primeFactors N z] at hp
      exact (chenSiftingPrime_lt_cutoff hp).trans_le hqD
    let A := chenDivisible (chenA N) q
    have hF : A.filter (·.Coprime P) = chenSifted N z A := by
      ext m
      simp only [chenSifted,Finset.mem_filter,chenRough_iff_coprime_product,P]
    have hb := (linearSieveBounds (chenSiftingProduct_squarefree N z) (by omega : 1<D/q)
      hp A (chenMediumMass N q) chenDivisorDensity).2
    rw [hF] at hb
    exact (Nat.cast_le.mpr (Finset.card_le_card (hs q))).trans hb
  have hmain : (∑ q∈Q,chenMediumMass N q*W q) =
      ((chenA N).card:ℝ)*quarterMediumPolynomial δ a N := by
    unfold quarterMediumPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq : q∣N
    · simp [chenMediumMass,hq]
    · simp only [chenMediumMass,hq,ite_false,chenDivisorDensity,W,P,D,z]
      ring
  have herr : (∑ q∈Q,E q) ≤ chenMediumError N D := by
    unfold chenMediumError
    calc
      _ = ∑ q∈Q, ∑ d∈(Finset.Ico 1 (D/q)).filter (fun d => d∣P),
          |chenMediumAPError N q d| := by
        apply Finset.sum_congr rfl
        intro q _
        exact quarterRemainder_eq_sum (chenDivisible (chenA N) q) (chenMediumMass N q)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hQ
        (fun _ _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  calc
    _ ≤ ∑ q∈Q,(chenMediumMass N q*W q + E q) := Finset.sum_le_sum hM
    _ ≤ _ := by rw [Finset.sum_add_distrib,hmain]; exact add_le_add le_rfl herr

private theorem quarterMediumScaled_comparison {θ a : ℝ} (hθ : 11/24<θ)
    (U : ℕ→ℝ) {N : ℕ} (hN : 2^24≤N) (hu : 0<U N) (ha : 1/8 ≤ a) {δ : ℝ} (hδ : 0≤δ)
    (h1 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      linearSieveMain true (chenSiftingProduct N (chenLowerCutoff N)) (chenPowerLevel θ N/q)
        chenDivisorDensity ≤ chenDensityProduct N (chenLowerCutoff N) *
          (linearSieveUpperFactor (chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))+δ))
    (h2 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      1≤chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))
    (h3 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      2/(Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ))≤
        2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))+δ) :
    (Real.log (N:ℝ)/U N)*quarterMediumPolynomial θ a N ≤
      (Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N +
        ((θ/2)*δ)*(Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N +
          chenDensityProduct N (chenLowerCutoff N)*Real.log (N:ℝ)/U N))*quarterMediumIdealSum θ a N := by
  let z := chenLowerCutoff N
  let D := chenPowerLevel θ N
  let L := Real.log (N:ℝ)
  let V := chenDensityProduct N z
  let A := Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N
  let B := V*L/U N
  have hn₂ : 2≤N := by omega
  have hn : (2:ℝ)≤N := by exact_mod_cast hn₂
  have hL : 0<L := Real.log_pos (by linarith)
  have hz₂ := (chenPowerLevel_cutoffs hθ hN).1
  have hzR : (2:ℝ)≤z := by exact_mod_cast hz₂
  have hzL : 0<Real.log (z:ℝ) := Real.log_pos (by linarith)
  have hV : 0≤V := quarterDensityProduct_nonneg ..
  have hA : 0≤A := by
    change 0≤Real.exp Real.eulerMascheroniConstant*(V*Real.log (z:ℝ)/U N)
    positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  have hθ₀ : 0<θ := by linarith
  unfold quarterMediumPolynomial quarterMediumIdealSum
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqold := quarterMediumSubset ha (by omega : 1 ≤ N) hq
  by_cases hq' : q∣N
  · simp [hq']
  · simp only [ite_eq_right hq']
    let K := 2/(θ-Real.log (q:ℝ)/L)
    have ⟨hlo,hhi⟩ := chenMediumLogPrimeRatio_bounds hn₂ hqold
    have hden : 0<θ-Real.log (q:ℝ)/L := by dsimp [L]; linarith
    have hKd : (θ/2)*K≥1 := by
      rw [show (θ/2)*K=θ/(θ-Real.log (q:ℝ)/L) by dsimp [K]; ring]
      apply (one_le_div hden).mpr
      change 0≤Real.log (q:ℝ)/L at hlo
      linarith only [hlo]
    have hqD : 0<Real.log ((D/q:ℕ):ℝ) :=
      ((show chenSieveParameter (D/q) z≥1 from h2 q hqold) |> (one_le_div hzL).mp)
        |> hzL.trans_le
    have hidentity :
        (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) =
          A*(2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*B := by
      change (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) =
        (Real.exp Real.eulerMascheroniConstant*(V*Real.log (z:ℝ)/U N))*
          (2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*(V*L/U N)
      unfold linearSieveUpperFactor chenSieveParameter
      field_simp
    have hk : 2/(Real.log ((D/q:ℕ):ℝ)/L)≤K+δ := h3 q hqold
    have hBgt := mul_le_mul_of_nonneg_left hKd (show 0≤δ*(A+B) by positivity)
    have hsum : A*(K+δ)+δ*B≤(A+((θ/2)*δ)*(A+B))*K := by
      nlinarith only [hBgt]
    have hg : 0≤chenDivisorDensity q := by unfold chenDivisorDensity; positivity
    have hh : (L/U N)*linearSieveMain true (chenSiftingProduct N z) (D/q) chenDivisorDensity ≤
        (A+((θ/2)*δ)*(A+B))*K := by
      calc _ ≤ (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) :=
                mul_le_mul_of_nonneg_left (h1 q hqold) (by positivity)
           _ = A*(2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*B := hidentity
           _ ≤ A*(K+δ)+δ*B := add_le_add_left (mul_le_mul_of_nonneg_left hk hA) _
           _ ≤ _ := hsum
    calc _ = chenDivisorDensity q*((L/U N)*
          linearSieveMain true (chenSiftingProduct N z) (D/q) chenDivisorDensity) := by ring
         _ ≤ chenDivisorDensity q*((A+((θ/2)*δ)*(A+B))*K) := mul_le_mul_of_nonneg_left hh hg
         _ = _ := by ring

private theorem quarterMediumNormalized_le {θ a : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (ha : 1/8 ≤ a) (ha' : a < 1/4)
    (U : ℕ→ℝ) (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : ChenCutoffNormalization U) (hP : ChenFloorRosserProfiles θ)
    (hM : Tendsto (quarterMediumIdealSum θ a) atTop (𝓝 (chenQuarterMediumCoeff θ a)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in chenEvenAtTop, quarterMediumPolynomial θ a N ≤
      (chenQuarterMediumCoeff θ a+ε)*(U N/Real.log (N:ℝ)) := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/(1/8)
  let M := chenQuarterMediumCoeff θ a
  let A (N : ℕ) := Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N
  let B (N : ℕ) := chenDensityProduct N (chenLowerCutoff N)*Real.log (N:ℝ)/U N
  have hθp : 0<θ := by linarith
  have hM₀ : 0≤M := quarterMediumCoeff_nonneg hθ ha ha'.le
  have hK : 0≤K := by dsimp [K]; positivity
  let C := (θ/2)*(1+K)*M
  have hC : 0≤C := by dsimp only [C]; positivity
  let δ := ε/(2*(C+1))
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hAe : Real.exp Real.eulerMascheroniConstant*Real.exp (-Real.eulerMascheroniConstant)=1 := by
    rw [←Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hA : Tendsto A chenEvenAtTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x:=Real.exp Real.eulerMascheroniConstant)).mul hV.1
    simpa only [hAe] using h
  have hB : Tendsto B chenEvenAtTop (𝓝 K) :=
    quarter_normalized_density_tendsto (by norm_num) hU hV.1
  have h := (hA.add (((tendsto_const_nhds (x:=(θ/2)*δ)).mul (hA.add hB)))).mul
    (hM.mono_left (show chenEvenAtTop≤atTop from inf_le_left))
  have ht : (1+((θ/2)*δ)*(1+K))*M<M+ε := by
    have he : δ*(2*(C+1))=ε := by dsimp only [δ]; field_simp
    dsimp only [C] at he
    nlinarith only [he,hδ,hε]
  have hcmp := h.eventually (Iio_mem_nhds ht)
  have hD := (chenActualSieveParameters_eventually_mem hθ hθ₂).filter_mono
    (show chenEvenAtTop≤atTop from inf_le_left)
  have hF := (chenMediumReciprocalFloor_eventually_le hθ hδ).filter_mono
    (show chenEvenAtTop≤atTop from inf_le_left)
  filter_upwards [hcmp,hD,hF,hU,hP δ hδ,quarterEven_log_pos,quarterEven_large (2^24)] with
    N hc hD hF hU hP hL hN
  have hu : 0<U N := by linarith
  have hs := quarterMediumScaled_comparison hθ U hN hu ha hδ.le hP.2.2
    (fun q hq => (hD.2.2 q hq).1) hF
  have hc' : (A N+((θ/2)*δ)*(A N+B N))*quarterMediumIdealSum θ a N<M+ε := hc
  have hh := mul_le_mul_of_nonneg_right (hs.trans hc'.le)
    (div_nonneg hu.le hL.le : 0≤U N/Real.log (N:ℝ))
  calc quarterMediumPolynomial θ a N =
      ((Real.log (N:ℝ)/U N)*quarterMediumPolynomial θ a N)*(U N/Real.log (N:ℝ)) := by field_simp
    _ ≤ _ := hh

private theorem quarterLowerNormalized {δ a η : ℝ}
    (hδ : 0<δ) (ha : 0<a) (ha' : a≤1) (hs₂ : 2<δ/a) (hs₄ : δ/a<4) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (chenQuarterLowerCoeff δ a-η)*(chenCanonicalU N/Real.log (N:ℝ)) ≤
        linearSieveMain false (chenSiftingProduct N (chenPowerLevel a N))
          (chenPowerLevel δ N) chenDivisorDensity := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/a
  let e := η/(2*K)
  have hK : 0<K := by dsimp [K]; positivity
  have he : 0<e := by dsimp [e]; positivity
  let V (N : ℕ) := chenDensityProduct N (chenPowerLevel a N) * Real.log (N:ℝ)/chenCanonicalU N
  let s (N : ℕ) := chenSieveParameter (chenPowerLevel δ N) (chenPowerLevel a N)
  have hV : Tendsto V chenEvenAtTop (𝓝 K) :=
    quarter_normalized_density_tendsto ha chenCanonicalU_eventually_ge_half (quarterLocalNormalization ha ha')
  have hs : Tendsto s atTop (𝓝 (δ/a)) := chenSieveParameter_tendsto hδ ha
  have hI := hs.eventually (Ioo_mem_nhds hs₂ hs₄)
  have hF : ContinuousAt linearSieveLowerFactor (δ/a) := by
    unfold linearSieveLowerFactor
    fun_prop (disch := intro H; linarith)
  have hlimit := hV.mul ((hF.tendsto.comp (hs.mono_left (show chenEvenAtTop≤atTop from inf_le_left))).sub
    (tendsto_const_nhds (x:=e)))
  have hcoeff : K*linearSieveLowerFactor (δ/a) = chenQuarterLowerCoeff δ a := by
    dsimp [K,linearSieveLowerFactor,chenQuarterLowerCoeff]
    rw [Real.exp_neg]
    field_simp
  have hKe : K*e=η/2 := by dsimp [e]; field_simp
  have hlt : chenQuarterLowerCoeff δ a-η < K*(linearSieveLowerFactor (δ/a)-e) := by
    rw [mul_sub,hcoeff,hKe]
    linarith
  have happrox := eventually_inf_principal.mp (hlimit.eventually (Ioi_mem_nhds hlt))
  filter_upwards [happrox,hI,quarterFixedRosser hδ ha he,
    eventually_inf_principal.mp chenCanonicalU_eventually_ge_half,
    eventually_inf_principal.mp quarterEven_log_pos] with N hh hI hp hu hL heven
  have hu' : 0<chenCanonicalU N := by linarith only [hu heven]
  have hL' := hL heven
  have hh' : chenQuarterLowerCoeff δ a-η < V N*(linearSieveLowerFactor (s N)-e) := hh heven
  calc
    _ ≤ (V N*(linearSieveLowerFactor (s N)-e))*(chenCanonicalU N/Real.log (N:ℝ)) :=
      mul_le_mul_of_nonneg_right hh'.le (by positivity)
    _ = chenDensityProduct N (chenPowerLevel a N)*(linearSieveLowerFactor (s N)-e) := by
      dsimp [V]
      field_simp [hL'.ne',hu'.ne']
    _ ≤ _ := (hp heven).2 hI.1.le hI.2.le

private theorem quarterUpperNormalized {δ η : ℝ}
    (hδ : 11/24<δ) (hδ' : δ<1/2) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      linearSieveMain true (chenSiftingProduct N (chenPowerLevel (1/4) N))
        (chenPowerLevel δ N) chenDivisorDensity ≤ (2/δ+η)*(chenCanonicalU N/Real.log (N:ℝ)) := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/(1/4)
  let e := η/(2*K)
  have hδ₀ : 0<δ := by linarith
  have hK : 0<K := by dsimp [K]; positivity
  have he : 0<e := by dsimp [e]; positivity
  let V (N : ℕ) := chenDensityProduct N (chenPowerLevel (1/4) N) * Real.log (N:ℝ)/chenCanonicalU N
  let s (N : ℕ) := chenSieveParameter (chenPowerLevel δ N) (chenPowerLevel (1/4) N)
  have hV : Tendsto V chenEvenAtTop (𝓝 K) :=
    quarter_normalized_density_tendsto (by norm_num) chenCanonicalU_eventually_ge_half
      (quarterLocalNormalization (by norm_num) (by norm_num))
  have hs : Tendsto s atTop (𝓝 (δ/(1/4))) := chenSieveParameter_tendsto hδ₀ (by norm_num)
  have hI := hs.eventually (Ioo_mem_nhds (show (1:ℝ)<δ/(1/4) by linarith)
    (show δ/(1/4)<3 by linarith))
  have hF : ContinuousAt linearSieveUpperFactor (δ/(1/4)) := by
    unfold linearSieveUpperFactor
    fun_prop (disch := positivity)
  have hlimit := hV.mul ((hF.tendsto.comp (hs.mono_left (show chenEvenAtTop≤atTop from inf_le_left))).add
    (tendsto_const_nhds (x:=e)))
  have hcoeff : K*linearSieveUpperFactor (δ/(1/4)) = 2/δ := by
    dsimp [K,linearSieveUpperFactor]
    rw [Real.exp_neg]
    field_simp
  have hKe : K*e=η/2 := by dsimp [e]; field_simp
  have hlt : K*(linearSieveUpperFactor (δ/(1/4))+e) < 2/δ+η := by
    rw [mul_add,hcoeff,hKe]
    linarith
  have happrox := eventually_inf_principal.mp (hlimit.eventually_lt_const hlt)
  filter_upwards [happrox,hI,quarterFixedRosser hδ₀ (a:=1/4) (by norm_num) he,
    eventually_inf_principal.mp chenCanonicalU_eventually_ge_half,
    eventually_inf_principal.mp quarterEven_log_pos] with N hh hI hp hu hL heven
  have hu' : 0<chenCanonicalU N := by linarith only [hu heven]
  have hL' := hL heven
  have hh' : V N*(linearSieveUpperFactor (s N)+e) < 2/δ+η := hh heven
  calc
    _ ≤ chenDensityProduct N (chenPowerLevel (1/4) N)*(linearSieveUpperFactor (s N)+e) :=
      (hp heven).1 hI.1 hI.2.le
    _ = (V N*(linearSieveUpperFactor (s N)+e))*(chenCanonicalU N/Real.log (N:ℝ)) := by
      dsimp [V]
      field_simp [hL'.ne',hu'.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right hh'.le (by positivity)

private theorem quarterScale_bounds {N : ℕ} (he : Even N) (hN : 2≤N) :
    0≤chenSieveScale chenCanonicalU N ∧ chenLogScale N≤2*chenSieveScale chenCanonicalU N := by
  have hu := chenCanonicalU_ge_half he hN
  have hu' : 0≤chenCanonicalU N := by linarith
  constructor
  · unfold chenSieveScale
    positivity
  · unfold chenLogScale chenSieveScale
    rw [←mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith only [mul_le_mul_of_nonneg_right hu (Nat.cast_nonneg (α:=ℝ) N)]

/-- Base and middle-prime terms at the quarter-power switch. The middle-prime
upper bound uses the original sieve on the shorter band. -/
theorem chen_quarter_prime_sieve_terms {δ a η : ℝ}
    (hδ : 11/24<δ) (hδ' : δ<1/2) (ha : 1/8≤a) (ha' : a<1/4)
    (hs₂ : 2<δ/a) (hs₄ : δ/a<4) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (chenQuarterLowerCoeff δ a-η)*chenSieveScale chenCanonicalU N ≤
        ((chenSifted N (chenPowerLevel a N) (chenA N)).card:ℝ) ∧
      (∑ q∈chenMediumPrimes (chenPowerLevel a N) (chenPowerLevel (1/4) N),
        ((chenSifted N (chenPowerLevel a N) (chenDivisible (chenA N) q)).card:ℝ)) ≤
        (chenQuarterMediumCoeff δ a+η)*chenSieveScale chenCanonicalU N := by
  let A := chenQuarterLowerCoeff δ a
  let M := chenQuarterMediumCoeff δ a
  have ha₀ : 0<a := by linarith
  have hδ₀ : 0<δ := by linarith
  have hA : 0<A := by
    unfold A chenQuarterLowerCoeff
    exact mul_pos (by positivity) (Real.log_pos (by linarith))
  have hM := quarterMediumCoeff_nonneg hδ ha ha'.le
  obtain ⟨e,he,_,heA,hbudgetA,hbudgetM,_⟩ :=
    chen_profile_budget hA hM (b:=0) (c:=0) le_rfl le_rfl hη
  have hm : Tendsto (quarterMediumIdealSum δ a) atTop (𝓝 M) := by
    have h := chen_prime_reciprocal_kernel_tendsto ha₀ ha' (show (1:ℝ)/4<δ by linarith)
    rw [chen_prime_band_kernel_integral_eq ha₀ ha'.le (show (1:ℝ)/4<δ by linarith)] at h
    exact h
  have hmnorm := eventually_inf_principal.mp (quarterMediumNormalized_le hδ hδ' ha ha'
    chenCanonicalU chenCanonicalU_eventually_ge_half chenCanonicalCutoffNormalization
    (chenFloorRosserProfiles_unconditional hδ hδ') hm he)
  obtain ⟨hPNT,hBV⟩ := chenPrimeAPDistribution_unconditional δ hδ hδ'
  have hLo := hPNT.eventually (Ioi_mem_nhds (show (1:ℝ)-e<1 by linarith))
  have hHi := hPNT.eventually_lt_const (show (1:ℝ)<1+e by linarith)
  filter_upwards [quarterLowerNormalized hδ₀ ha₀ (by linarith) hs₂ hs₄ he,hmnorm,hBV e he,hLo,hHi,
    eventually_ge_atTop (2^24:ℕ),(chenPowerLevel_tendsto_atTop hδ₀).eventually_ge_atTop 2]
    with N hl hm hBV hLo hHi hN hD heven
  have hN₂ : 2≤N := by omega
  let T := chenSieveScale chenCanonicalU N
  let X := (N:ℝ)/Real.log (N:ℝ)
  let U := chenCanonicalU N/Real.log (N:ℝ)
  have hX : 0<X := by dsimp [X]; exact div_pos (by positivity) (Real.log_pos (Nat.one_lt_cast.mpr hN₂))
  have hU : 0≤U := by
    have := chenCanonicalU_ge_half heven hN₂
    dsimp [U]
    positivity
  have hT : X*U=T := by dsimp [T,X,U,chenSieveScale]; ring
  have ⟨hT₀,hscale⟩ := quarterScale_bounds heven hN₂
  have hErr := mul_le_mul_of_nonneg_left hscale he.le
  have hAl := ((lt_div_iff₀ hX).mp hLo).le
  have hAh := ((div_lt_iff₀ hX).mp hHi).le
  have hzD : chenPowerLevel a N ≤ chenPowerLevel δ N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega))
      (by linarith only [(lt_div_iff₀ ha₀).mp hs₂,ha₀]))
  have hLF := (quarterFiniteSieve (N:=N) hzD (show 1<chenPowerLevel δ N by omega) (chenA N)).1
  have hMF := quarterMediumFinite hδ ha hN
  have hLower : ((1-e)*(A-e))*T ≤ (chenA N).card *
      linearSieveMain false (chenSiftingProduct N (chenPowerLevel a N)) (chenPowerLevel δ N) chenDivisorDensity := by
    calc
      _ = ((1-e)*X)*((A-e)*U) := by rw [←hT]; ring
      _ ≤ (chenA N).card*((A-e)*U) := mul_le_mul_of_nonneg_right hAl (mul_nonneg (sub_nonneg.mpr heA) hU)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hl heven) (Nat.cast_nonneg _)
  have hMedium : (chenA N).card * quarterMediumPolynomial δ a N ≤ ((1+e)*(M+e))*T := by
    calc
      _ ≤ (chenA N).card*((M+e)*U) := mul_le_mul_of_nonneg_left (hm heven) (Nat.cast_nonneg _)
      _ ≤ ((1+e)*X)*((M+e)*U) := mul_le_mul_of_nonneg_right hAh (by positivity)
      _ = _ := by rw [←hT]; ring
  have hB₁ := mul_le_mul_of_nonneg_right hbudgetA hT₀
  have hB₂ := mul_le_mul_of_nonneg_right hbudgetM hT₀
  have hBV' := hBV heven
  unfold chenPrimeAPError at hBV'
  dsimp only [A,M,T] at hLower hMedium hB₁ hB₂
  exact ⟨by linarith only [hB₁,hLF,hLower,hBV'.1,hErr],
    by linarith only [hB₂,hMF,hMedium,hBV'.2,hErr]⟩

/-- Normalized upper sieve for any switched carrier with a mass bound and
an unconditional reduced-modulus remainder bound. -/
theorem chen_quarter_switched_sieve_bound {δ C η : ℝ} (hδ : 11/24<δ) (hδ' : δ<1/2)
    (hC : 0≤C) (hη : 0<η) (B : ℕ→Finset ℕ)
    (hMass : ∀ e : ℝ, 0<e → ∀ᶠ N : ℕ in atTop, Even N →
      ((B N).card:ℝ) ≤ (C+e)*((N:ℝ)/Real.log (N:ℝ)))
    (hBV : ∀ e : ℝ, 0<e → ∀ᶠ N : ℕ in atTop, Even N →
      chenReducedError N (chenPowerLevel δ N) (chenAPError (B N) (B N).card) ≤ e*chenLogScale N) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ((chenSifted N (chenPowerLevel (1/4) N) (B N)).card:ℝ) ≤
        ((2/δ)*C+η)*chenSieveScale chenCanonicalU N := by
  have hδ₀ : 0<δ := by linarith
  obtain ⟨e,he,_,_,_,_,hbudget⟩ := chen_profile_budget (a:=1) (m:=0) (b:=2/δ) (c:=C)
    zero_lt_one le_rfl (by positivity) hC hη
  filter_upwards [hMass e he,hBV e he,quarterUpperNormalized hδ hδ' he,
    eventually_ge_atTop (2:ℕ),(chenPowerLevel_tendsto_atTop hδ₀).eventually_ge_atTop 2]
    with N hMass hBV hProf hN hD heven
  let T := chenSieveScale chenCanonicalU N
  let X := (N:ℝ)/Real.log (N:ℝ)
  let U := chenCanonicalU N/Real.log (N:ℝ)
  have hU : 0≤U := by
    have := chenCanonicalU_ge_half heven hN
    dsimp [U]
    positivity
  have hT : X*U=T := by dsimp [T,X,U,chenSieveScale]; ring
  have ⟨hT₀,hscale⟩ := quarterScale_bounds heven hN
  have hzD : chenPowerLevel (1/4) N ≤ chenPowerLevel δ N := Nat.floor_le_floor
    (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (by omega)) (by linarith))
  have hFin := (quarterFiniteSieve (N:=N) hzD (show 1<chenPowerLevel δ N by omega) (B N)).2
  have hMain : (B N).card * linearSieveMain true (chenSiftingProduct N (chenPowerLevel (1/4) N))
      (chenPowerLevel δ N) chenDivisorDensity ≤ ((C+e)*(2/δ+e))*T := by
    calc
      _ ≤ (B N).card*((2/δ+e)*U) := mul_le_mul_of_nonneg_left (hProf heven) (Nat.cast_nonneg _)
      _ ≤ ((C+e)*X)*((2/δ+e)*U) := mul_le_mul_of_nonneg_right (hMass heven) (by positivity)
      _ = _ := by rw [←hT]; ring
  have hB := mul_le_mul_of_nonneg_right hbudget hT₀
  have hErr := mul_le_mul_of_nonneg_left hscale he.le
  linarith only [hFin,hMain,hBV heven,hB,hErr]

end FareyGoldbach
