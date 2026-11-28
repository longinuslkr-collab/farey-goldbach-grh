import FareyGoldbach.ChenActualSieveParameters
import FareyGoldbach.ChenSieveNormalization
import FareyGoldbach.ChenConditional
import FareyGoldbach.ChenProfileFactors

/-! # Substitution of the local and prime-sum limits into the Chen coefficients -/

open Filter Set
open scoped Topology Classical

namespace FareyGoldbach

def chenEvenAtTop : Filter ℕ := atTop ⊓ 𝓟 {N : ℕ | Even N}

noncomputable def chenLocalNormalized (U : ℕ→ℝ) (a : ℝ) (N : ℕ) : ℝ :=
  chenDensityProduct N (chenPowerLevel a N)*Real.log (chenPowerLevel a N : ℝ)/U N

def ChenCutoffNormalization (U : ℕ→ℝ) : Prop :=
  Tendsto (chenLocalNormalized U (1/8)) chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) ∧
  Tendsto (chenLocalNormalized U (1/3)) chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

/-- Profile approximations before multiplying by the local density or summing over
the middle primes. The moduli in the middle branch are the actual quotients. -/
def ChenFloorRosserProfiles (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ N in chenEvenAtTop,
    let D := chenPowerLevel θ N
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    chenDensityProduct N z*(linearSieveLowerFactor (chenSieveParameter D z)-ε)≤chenLowerPolynomial θ N ∧
    chenSwitchedPolynomial θ N≤chenDensityProduct N y*(linearSieveUpperFactor (chenSieveParameter D y)+ε) ∧
    ∀ q∈chenMediumPrimes z y,
      linearSieveMain true (chenSiftingProduct N z) (D/q) chenDivisorDensity ≤
        chenDensityProduct N z*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+ε)

noncomputable def chenMediumIdealSum (θ : ℝ) (N : ℕ) : ℝ :=
  ∑ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
    if q∣N then 0 else chenDivisorDensity q*(2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ)))

private theorem chenDensityProduct_nonneg (N w : ℕ) : 0≤chenDensityProduct N w := by
  unfold chenDensityProduct
  apply Finset.prod_nonneg
  intro p hp
  have h := (Finset.mem_filter.mp hp).2.1.pos
  have hφ : (1:ℝ)≤p.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr h)
  exact sub_nonneg.mpr ((div_le_one (zero_lt_one.trans_le hφ)).2 hφ)

private theorem chenEven_large (k : ℕ) : ∀ᶠ N in chenEvenAtTop, k≤N :=
  (eventually_ge_atTop k).filter_mono inf_le_left

private theorem chenEven_log_pos : ∀ᶠ N : ℕ in chenEvenAtTop, 0<Real.log (N:ℝ) := by
  filter_upwards [chenEven_large 2] with N hN
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  exact Real.log_pos (by linarith)

private theorem normalized_density_tendsto {U : ℕ→ℝ} {a : ℝ} (ha : 0<a)
    (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : Tendsto (chenLocalNormalized U a) chenEvenAtTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))) :
    Tendsto (fun N => chenDensityProduct N (chenPowerLevel a N)*Real.log (N:ℝ)/U N)
      chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/a)) := by
  have h := hV.div ((chenLogPowerLevel_tendsto ha).mono_left inf_le_left) ha.ne'
  apply h.congr'
  have hw := ((chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop (2:ℕ)).filter_mono
    (show chenEvenAtTop≤atTop from inf_le_left)
  filter_upwards [chenEven_log_pos,hw,hU] with N hL hw hU'
  have hw' : (2:ℝ)≤chenPowerLevel a N := by exact_mod_cast hw
  have hlw : 0<Real.log (chenPowerLevel a N : ℝ) := Real.log_pos (by linarith)
  have hpos : 0<U N := by linarith
  change (chenDensityProduct N (chenPowerLevel a N)*Real.log (chenPowerLevel a N:ℝ)/U N)/
    (Real.log (chenPowerLevel a N:ℝ)/Real.log (N:ℝ)) = _
  field_simp

private theorem chenLowerNormalized_le {θ : ℝ} (hθ : 11/24<θ) (U : ℕ→ℝ)
    (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : ChenCutoffNormalization U) (hP : ChenFloorRosserProfiles θ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in chenEvenAtTop, (chenLowerMainCoeff θ-ε)*(U N/Real.log (N:ℝ)) ≤
      chenLowerPolynomial θ N := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/(1/8)
  have hK : 0<K := by dsimp [K]; positivity
  let δ := ε/(2*K)
  have hδ : 0<δ := by dsimp [δ]; positivity
  let F : ℕ→ℝ := fun N => linearSieveLowerFactor
    (chenSieveParameter (chenPowerLevel θ N) (chenLowerCutoff N))
  let V : ℕ→ℝ := fun N => chenDensityProduct N (chenLowerCutoff N)*Real.log (N:ℝ)/U N
  have hν : Tendsto V chenEvenAtTop (𝓝 K) :=
    normalized_density_tendsto (by norm_num) hU hV.1
  have hθp : 0<θ := by linarith
  have hcon : ContinuousAt linearSieveLowerFactor (8*θ) := by
    unfold linearSieveLowerFactor
    fun_prop (disch := intro H; linarith)
  have hparam : Tendsto (fun N => chenSieveParameter (chenPowerLevel θ N) (chenLowerCutoff N))
      chenEvenAtTop (𝓝 (8*θ)) := by
    have h := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/8)).mono_left
      (show chenEvenAtTop≤atTop from inf_le_left)
    rw [show θ/(1/8)=8*θ by ring] at h
    exact h
  have hf : Tendsto F chenEvenAtTop (𝓝 (linearSieveLowerFactor (8*θ))) := hcon.tendsto.comp hparam
  have ht := hν.mul (hf.sub (tendsto_const_nhds (x:=δ)))
  have hc : K*linearSieveLowerFactor (8*θ) = chenLowerMainCoeff θ := by
    convert chen_lower_profile_eq hθ using 1
    dsimp [K]
    ring
  have hKδ : K*δ=ε/2 := by dsimp [δ]; field_simp
  have hlt : chenLowerMainCoeff θ-ε<K*(linearSieveLowerFactor (8*θ)-δ) := by
    rw [mul_sub,hc,hKδ]
    linarith only [hε]
  have he := ht.eventually (Ioi_mem_nhds hlt)
  filter_upwards [he,hP δ hδ,hU,chenEven_log_pos] with N ht hp hu hL
  have hu' : 0<U N := by linarith
  have ht' : chenLowerMainCoeff θ-ε<V N*(F N-δ) := ht
  calc _ ≤ (V N*(F N-δ))*(U N/Real.log (N:ℝ)) :=
        mul_le_mul_of_nonneg_right ht'.le (div_nonneg hu'.le hL.le)
      _ = chenDensityProduct N (chenLowerCutoff N)*(F N-δ) := by dsimp only [V]; field_simp
      _ ≤ _ := hp.1

private theorem chenSwitchedNormalized_le {θ : ℝ} (hθ : 11/24<θ) (U : ℕ→ℝ)
    (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : ChenCutoffNormalization U) (hP : ChenFloorRosserProfiles θ)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in chenEvenAtTop, chenSwitchedPolynomial θ N ≤
      (2/θ+ε)*(U N/Real.log (N:ℝ)) := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/(1/3)
  have hK : 0<K := by dsimp [K]; positivity
  let δ := ε/(2*K)
  have hδ : 0<δ := by dsimp [δ]; positivity
  let F : ℕ→ℝ := fun N => linearSieveUpperFactor
    (chenSieveParameter (chenPowerLevel θ N) (chenUpperCutoff N))
  let V : ℕ→ℝ := fun N => chenDensityProduct N (chenUpperCutoff N)*Real.log (N:ℝ)/U N
  have hν : Tendsto V chenEvenAtTop (𝓝 K) :=
    normalized_density_tendsto (by norm_num) hU hV.2
  have hθp : 0<θ := by linarith
  have hcon : ContinuousAt linearSieveUpperFactor (3*θ) := by
    unfold linearSieveUpperFactor
    fun_prop (disch := positivity)
  have hparam : Tendsto (fun N => chenSieveParameter (chenPowerLevel θ N) (chenUpperCutoff N))
      chenEvenAtTop (𝓝 (3*θ)) := by
    have h := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/3)).mono_left
      (show chenEvenAtTop≤atTop from inf_le_left)
    rw [show θ/(1/3)=3*θ by ring] at h
    exact h
  have hf : Tendsto F chenEvenAtTop (𝓝 (linearSieveUpperFactor (3*θ))) := hcon.tendsto.comp hparam
  have ht := hν.mul (hf.add (tendsto_const_nhds (x:=δ)))
  have hc : K*linearSieveUpperFactor (3*θ) = 2/θ := by
    unfold linearSieveUpperFactor
    dsimp only [K]
    rw [Real.exp_neg]
    field_simp
  have hKδ : K*δ=ε/2 := by dsimp [δ]; field_simp
  have hlt : K*(linearSieveUpperFactor (3*θ)+δ)<2/θ+ε := by
    rw [mul_add,hc,hKδ]
    linarith only [hε]
  have he := ht.eventually (Iio_mem_nhds hlt)
  filter_upwards [he,hP δ hδ,hU,chenEven_log_pos] with N ht hp hu hL
  have hu' : 0<U N := by linarith
  have ht' : V N*(F N+δ)<2/θ+ε := ht
  calc _ ≤ chenDensityProduct N (chenUpperCutoff N)*(F N+δ) := hp.2.1
      _ = (V N*(F N+δ))*(U N/Real.log (N:ℝ)) := by dsimp only [V]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ht'.le (div_nonneg hu'.le hL.le)

private theorem chenMediumCoeff_nonneg {θ : ℝ} (hθ : 11/24<θ) :
    0≤chenMediumMainCoeff θ := by
  have hθp : 0<θ := by linarith
  have h : 0<3*θ-1 := by linarith
  unfold chenMediumMainCoeff
  exact mul_nonneg (by positivity) (Real.log_nonneg ((one_le_div h).2 (by linarith)))

private theorem chenMediumScaled_comparison {θ : ℝ} (hθ : 11/24<θ)
    (U : ℕ→ℝ) {N : ℕ} (hN : 2^24≤N) (hu : 0<U N) {δ : ℝ} (hδ : 0≤δ)
    (h1 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      linearSieveMain true (chenSiftingProduct N (chenLowerCutoff N)) (chenPowerLevel θ N/q)
        chenDivisorDensity ≤ chenDensityProduct N (chenLowerCutoff N) *
          (linearSieveUpperFactor (chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))+δ))
    (h2 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      1≤chenSieveParameter (chenPowerLevel θ N/q) (chenLowerCutoff N))
    (h3 : ∀ q∈chenMediumPrimes (chenLowerCutoff N) (chenUpperCutoff N),
      2/(Real.log ((chenPowerLevel θ N/q:ℕ):ℝ)/Real.log (N:ℝ))≤
        2/(θ-Real.log (q:ℝ)/Real.log (N:ℝ))+δ) :
    (Real.log (N:ℝ)/U N)*chenMediumPolynomial θ N ≤
      (Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N +
        ((θ/2)*δ)*(Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N +
          chenDensityProduct N (chenLowerCutoff N)*Real.log (N:ℝ)/U N))*chenMediumIdealSum θ N := by
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
  have hV : 0≤V := chenDensityProduct_nonneg ..
  have hA : 0≤A := by
    change 0≤Real.exp Real.eulerMascheroniConstant*(V*Real.log (z:ℝ)/U N)
    positivity
  have hB : 0≤B := by dsimp only [B]; positivity
  have hθ₀ : 0<θ := by linarith
  unfold chenMediumPolynomial chenMediumIdealSum
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  by_cases hq' : q∣N
  · simp [hq']
  · simp only [ite_eq_right hq']
    let K := 2/(θ-Real.log (q:ℝ)/L)
    have ⟨hlo,hhi⟩ := chenMediumLogPrimeRatio_bounds hn₂ hq
    have hden : 0<θ-Real.log (q:ℝ)/L := by dsimp [L]; linarith
    have hKd : (θ/2)*K≥1 := by
      rw [show (θ/2)*K=θ/(θ-Real.log (q:ℝ)/L) by dsimp [K]; ring]
      apply (one_le_div hden).mpr
      change 0≤Real.log (q:ℝ)/L at hlo
      linarith only [hlo]
    have hqD : 0<Real.log ((D/q:ℕ):ℝ) :=
      ((show chenSieveParameter (D/q) z≥1 from h2 q hq) |> (one_le_div hzL).mp)
        |> hzL.trans_le
    have hidentity :
        (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) =
          A*(2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*B := by
      change (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) =
        (Real.exp Real.eulerMascheroniConstant*(V*Real.log (z:ℝ)/U N))*
          (2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*(V*L/U N)
      unfold linearSieveUpperFactor chenSieveParameter
      field_simp
    have hk : 2/(Real.log ((D/q:ℕ):ℝ)/L)≤K+δ := h3 q hq
    have hBgt := mul_le_mul_of_nonneg_left hKd (show 0≤δ*(A+B) by positivity)
    have hsum : A*(K+δ)+δ*B≤(A+((θ/2)*δ)*(A+B))*K := by
      nlinarith only [hBgt]
    have hg : 0≤chenDivisorDensity q := by unfold chenDivisorDensity; positivity
    have hh : (L/U N)*linearSieveMain true (chenSiftingProduct N z) (D/q) chenDivisorDensity ≤
        (A+((θ/2)*δ)*(A+B))*K := by
      calc _ ≤ (L/U N)*(V*(linearSieveUpperFactor (chenSieveParameter (D/q) z)+δ)) :=
                mul_le_mul_of_nonneg_left (h1 q hq) (by positivity)
           _ = A*(2/(Real.log ((D/q:ℕ):ℝ)/L))+δ*B := hidentity
           _ ≤ A*(K+δ)+δ*B := add_le_add_left (mul_le_mul_of_nonneg_left hk hA) _
           _ ≤ _ := hsum
    calc _ = chenDivisorDensity q*((L/U N)*
          linearSieveMain true (chenSiftingProduct N z) (D/q) chenDivisorDensity) := by ring
         _ ≤ chenDivisorDensity q*((A+((θ/2)*δ)*(A+B))*K) := mul_le_mul_of_nonneg_left hh hg
         _ = _ := by ring

private theorem chenMediumNormalized_le {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (U : ℕ→ℝ) (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : ChenCutoffNormalization U) (hP : ChenFloorRosserProfiles θ)
    (hM : Tendsto (chenMediumIdealSum θ) atTop (𝓝 (chenMediumMainCoeff θ)))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in chenEvenAtTop, chenMediumPolynomial θ N ≤
      (chenMediumMainCoeff θ+ε)*(U N/Real.log (N:ℝ)) := by
  let K := Real.exp (-Real.eulerMascheroniConstant)/(1/8)
  let M := chenMediumMainCoeff θ
  let A (N : ℕ) := Real.exp Real.eulerMascheroniConstant*chenLocalNormalized U (1/8) N
  let B (N : ℕ) := chenDensityProduct N (chenLowerCutoff N)*Real.log (N:ℝ)/U N
  have hθp : 0<θ := by linarith
  have hM₀ : 0≤M := chenMediumCoeff_nonneg hθ
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
    normalized_density_tendsto (by norm_num) hU hV.1
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
  filter_upwards [hcmp,hD,hF,hU,hP δ hδ,chenEven_log_pos,chenEven_large (2^24)] with
    N hc hD hF hU hP hL hN
  have hu : 0<U N := by linarith
  have hs := chenMediumScaled_comparison hθ U hN hu hδ.le hP.2.2
    (fun q hq => (hD.2.2 q hq).1) hF
  have hc' : (A N+((θ/2)*δ)*(A N+B N))*chenMediumIdealSum θ N<M+ε := hc
  have hh := mul_le_mul_of_nonneg_right (hs.trans hc'.le)
    (div_nonneg hu.le hL.le : 0≤U N/Real.log (N:ℝ))
  calc chenMediumPolynomial θ N =
      ((Real.log (N:ℝ)/U N)*chenMediumPolynomial θ N)*(U N/Real.log (N:ℝ)) := by field_simp
    _ ≤ _ := hh

/-- The numerical comparisons follow from the three analytic inputs. The
weighted prime sum, normalization and finite Rosser profiles are separate. -/
theorem chenRosserMainComparisons_of_profiles {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (U : ℕ→ℝ) (hU : ∀ᶠ N in chenEvenAtTop, (1:ℝ)/2≤U N)
    (hV : ChenCutoffNormalization U) (hP : ChenFloorRosserProfiles θ)
    (hM : Tendsto (chenMediumIdealSum θ) atTop (𝓝 (chenMediumMainCoeff θ))) :
    ChenRosserMainComparisons θ U := by
  intro ε hε
  have hf : ∀ᶠ N in chenEvenAtTop,
      (chenLowerMainCoeff θ-ε)*(U N/Real.log (N:ℝ))≤chenLowerPolynomial θ N ∧
      chenMediumPolynomial θ N≤(chenMediumMainCoeff θ+ε)*(U N/Real.log (N:ℝ)) ∧
      chenSwitchedPolynomial θ N≤(2/θ+ε)*(U N/Real.log (N:ℝ)) :=
    (chenLowerNormalized_le hθ U hU hV hP hε).and
      ((chenMediumNormalized_le hθ hθ₂ U hU hV hP hM hε).and
        (chenSwitchedNormalized_le hθ U hU hV hP hε))
  exact eventually_inf_principal.mp hf

end FareyGoldbach
