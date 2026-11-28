import FareyGoldbach.ChenAPCutoffNormalization
import FareyGoldbach.ChenAPMediumEnvelope

/-! # Unconditional Rosser main-term comparisons for Chen progressions -/

open Filter Set
open scoped Topology

namespace FareyGoldbach

private theorem ap_density_log_tendsto (r : ℕ→ℕ) (hr : ChenAPModuli r) {a : ℝ}
    (ha : 0<a) (ha₁ : a≤1) :
    Tendsto (fun N : ℕ => chenDensityProduct (r N*N) (chenPowerLevel a N)*Real.log (N:ℝ)/
      chenCanonicalU (r N*N)) chenEvenAtTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)/a)) := by
  have h := (chenAPCutoff_tendsto r hr ha ha₁).div
    ((chenLogPowerLevel_tendsto ha).mono_left inf_le_left) ha.ne'
  apply h.congr'
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop (2:ℕ),(chenPowerLevel_tendsto_atTop ha).eventually_ge_atTop 2]
    with N hN hw he
  have hn : (2:ℝ)≤N := by exact_mod_cast hN
  have hw' : (2:ℝ)≤chenPowerLevel a N := by exact_mod_cast hw
  have hL := Real.log_pos (by linarith : (1:ℝ)<N)
  have hW := Real.log_pos (by linarith : (1:ℝ)<chenPowerLevel a N)
  change (_*Real.log (chenPowerLevel a N:ℝ)/_)/(Real.log (chenPowerLevel a N:ℝ)/Real.log (N:ℝ))=_
  field_simp

private theorem ap_comparisons_along {θ : ℝ} (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (r : ℕ→ℕ) (hr : ChenAPModuli r) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in chenEvenAtTop,
      (chenLowerMainCoeff θ-ε)*(chenCanonicalU (r N*N)/Real.log (N:ℝ))≤chenAPLowerPolynomial θ N (r N*N) ∧
      chenAPMediumPolynomial θ N (r N*N)≤(chenMediumMainCoeff θ+ε)*(chenCanonicalU (r N*N)/Real.log (N:ℝ)) ∧
      chenAPSwitchedPolynomial θ N (r N*N)≤(2/θ+ε)*(chenCanonicalU (r N*N)/Real.log (N:ℝ)) := by
  let V (a : ℝ) (N : ℕ) := chenDensityProduct (r N*N) (chenPowerLevel a N)*Real.log (N:ℝ)/chenCanonicalU (r N*N)
  let K (a : ℝ) := Real.exp (-Real.eulerMascheroniConstant)/a
  let c := Real.exp Real.eulerMascheroniConstant*(1/8)
  let J := Real.log (8/3)
  let A := K (1/8)*(c+1)*J
  let E := 1+K (1/8)+K (1/3)+A
  have hz : 0<K (1/8) := by dsimp [K]; positivity
  have hy : 0<K (1/3) := by dsimp [K]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hJ : 0≤J := Real.log_nonneg (by norm_num)
  have hA : 0≤A := by dsimp [A]; positivity
  have hE : 0<E := by dsimp [E]; positivity
  let δ := ε/(2*E)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδE : δ*E=ε/2 := by dsimp [δ]; field_simp
  have hδsmall (t : ℝ) (ht : t≤E) : δ*t<ε := by
    linarith only [mul_le_mul_of_nonneg_left ht hδ.le,hδE,hε]
  have hzδ := hδsmall (K (1/8)) (by dsimp [E]; linarith only [hy,hA])
  have hyδ := hδsmall (K (1/3)) (by dsimp [E]; linarith only [hz,hA])
  have hAδ := hδsmall A (by dsimp [E]; linarith only [hz,hy])
  have hV (a : ℝ) (ha : 0<a) (ha₁ : a≤1) : Tendsto (V a) chenEvenAtTop (𝓝 (K a)) :=
    ap_density_log_tendsto r hr ha ha₁
  have hθp : 0<θ := by linarith
  have hL : ContinuousAt linearSieveLowerFactor (8*θ) := by
    unfold linearSieveLowerFactor
    fun_prop (disch := intro he; linarith)
  have hU : ContinuousAt linearSieveUpperFactor (3*θ) := by
    unfold linearSieveUpperFactor
    fun_prop (disch := positivity)
  have hsz := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/8)).mono_left
    (show chenEvenAtTop≤atTop from inf_le_left)
  have hsy := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/3)).mono_left
    (show chenEvenAtTop≤atTop from inf_le_left)
  rw [show θ/(1/8)=8*θ by ring] at hsz
  rw [show θ/(1/3)=3*θ by ring] at hsy
  have hFz := (hV (1/8) (by norm_num) (by norm_num)).mul
    ((hL.tendsto.comp hsz).sub_const δ)
  have hFy := (hV (1/3) (by norm_num) (by norm_num)).mul
    ((hU.tendsto.comp hsy).add_const δ)
  have hLC : K (1/8)*linearSieveLowerFactor (8*θ)=chenLowerMainCoeff θ := by
    convert chen_lower_profile_eq hθ using 1
    dsimp [K]; ring
  have hSC : K (1/3)*linearSieveUpperFactor (3*θ)=2/θ := by
    unfold linearSieveUpperFactor
    dsimp only [K]; rw [Real.exp_neg]; field_simp
  have hlo := hFz.eventually (Ioi_mem_nhds (show chenLowerMainCoeff θ-ε<
      K (1/8)*(linearSieveLowerFactor (8*θ)-δ) by rw [mul_sub,hLC]; linarith only [hzδ]))
  have hsw := hFy.eventually (Iio_mem_nhds (show K (1/3)*(linearSieveUpperFactor (3*θ)+δ)<2/θ+ε by
    rw [mul_add,hSC]; linarith only [hyδ]))
  have hC : Tendsto chenAPMediumScale chenEvenAtTop (𝓝 c) :=
    ((chenLogPowerLevel_tendsto (by norm_num : (0:ℝ)<1/8)).mono_left inf_le_left).const_mul _
  have hm : Tendsto chenAPMediumMass chenEvenAtTop (𝓝 J) := chen_medium_totient_tendsto.mono_left inf_le_left
  have hi : Tendsto (chenMediumIdealSum θ) chenEvenAtTop (𝓝 (chenMediumMainCoeff θ)) :=
    (chen_medium_reciprocal_tendsto (by linarith : 1/3<θ)).mono_left inf_le_left
  have hmed := (hV (1/8) (by norm_num) (by norm_num)).mul
    ((hC.mul hi).add (((hC.add_const 1).const_mul δ).mul hm))
  have hKc : K (1/8)*c=1 := by dsimp [K,c]; rw [Real.exp_neg]; field_simp
  have hmc : K (1/8)*(c*chenMediumMainCoeff θ+δ*(c+1)*J) =
      chenMediumMainCoeff θ+δ*A := by
    dsimp only [A]; linear_combination (chenMediumMainCoeff θ)*hKc
  have hmid := hmed.eventually (Iio_mem_nhds (show K (1/8)*(c*chenMediumMainCoeff θ+δ*(c+1)*J)<
      chenMediumMainCoeff θ+ε by rw [hmc]; linarith only [hAδ]))
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_inf_principal.mp hlo,eventually_inf_principal.mp hmid,
    eventually_inf_principal.mp hsw,chenAP_floor_profiles hθ hθ₂ hδ,
    chenActualSieveParameters_eventually_mem hθ hθ₂,chenMediumReciprocalFloor_eventually_le hθ hδ,
    eventually_ge_atTop (2^24:ℕ)] with N hlo hmid hsw hp hparams hfloor hN he
  let m := r N*N
  let L := Real.log (N:ℝ)
  let U := chenCanonicalU m
  have hn₂ : 2≤N := by omega
  have hnn : N≤m := Nat.le_mul_of_pos_left _ (hr N hn₂).1
  have hem : Even m := Even.mul_left he _
  have hpos := chenCanonicalU_ge_half hem (hn₂.trans hnn)
  have hu : 0<U := by dsimp [U]; linarith only [hpos]
  have hNr : (2:ℝ)≤N := by exact_mod_cast hn₂
  have hl : 0<L := Real.log_pos (by linarith)
  have hscale : 0≤U/L := div_nonneg hu.le hl.le
  have hcancel (a F : ℝ) : (V a N*F)*(U/L)=chenDensityProduct m (chenPowerLevel a N)*F := by
    change (chenDensityProduct m _*L/U*F)*(U/L)=_
    field_simp
  obtain ⟨hpl,hps,hpm⟩ := hp m hem
  have h₁ := mul_le_mul_of_nonneg_right (le_of_lt (hlo he)) hscale
  have h₂ := mul_le_mul_of_nonneg_right (le_of_lt (hmid he)) hscale
  have h₃ := mul_le_mul_of_nonneg_right (le_of_lt (hsw he)) hscale
  refine ⟨h₁.trans ((hcancel (1/8) _).le.trans hpl),?_,hps.trans ((hcancel (1/3) _).ge.trans h₃)⟩
  exact (chenAP_medium_envelope hθ hδ.le hN (dvd_mul_left N (r N)) hpm
    (fun q hq => (hparams.2.2 q hq).1) hfloor).trans ((hcancel (1/8) _).ge.trans h₂)

/-- The same cutoff threshold works simultaneously for all auxiliary moduli up to the target. -/
theorem chenAPRosserMainComparisons_unconditional {θ : ℝ} (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ N : ℕ in atTop, Even N → ∀ r : ℕ, 0<r → r≤N →
      (chenLowerMainCoeff θ-ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ))≤chenAPLowerPolynomial θ N (r*N) ∧
      chenAPMediumPolynomial θ N (r*N)≤(chenMediumMainCoeff θ+ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ)) ∧
      chenAPSwitchedPolynomial θ N (r*N)≤(2/θ+ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ)) := by
  classical
  intro ε hε
  let P (N r : ℕ) : Prop :=
    (chenLowerMainCoeff θ-ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ))≤chenAPLowerPolynomial θ N (r*N) ∧
    chenAPMediumPolynomial θ N (r*N)≤(chenMediumMainCoeff θ+ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ)) ∧
    chenAPSwitchedPolynomial θ N (r*N)≤(2/θ+ε)*(chenCanonicalU (r*N)/Real.log (N:ℝ))
  let r (N : ℕ) := if h : ∃ k, 0<k ∧ k≤N ∧ ¬P N k then h.choose else 1
  have hr : ChenAPModuli r := by
    intro N hN
    dsimp only [r]
    split_ifs with h
    · exact ⟨h.choose_spec.1,h.choose_spec.2.1⟩
    · omega
  have h := eventually_inf_principal.mp (ap_comparisons_along hθ₁ hθ₂ r hr hε)
  filter_upwards [h] with N h he k hk hkN
  change P N k
  by_contra hb
  have ht : ∃ j, 0<j ∧ j≤N ∧ ¬P N j := ⟨k,hk,hkN,hb⟩
  have hg : P N (r N) := h he
  exact ht.choose_spec.2.2 (by simpa only [r,dite_eq_left ht] using hg)

end FareyGoldbach
