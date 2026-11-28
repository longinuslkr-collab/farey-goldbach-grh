import FareyGoldbach.TwinChenNormalization
import FareyGoldbach.TwinChenMedium

/-! # Unconditional Rosser comparisons for the shifted-prime carrier -/

open Filter Set
open scoped Topology

namespace FareyGoldbach

private theorem twin_comparisons_along {d θ : ℝ} (hd₀ : 0≤d) (hd : d<1/8) (hθ : 11/24<θ) (hθ₂ : θ<1/2)
    (r : ℕ→ℕ) (hr : ∀ M, 1≤M → 0<r M ∧ (r M:ℝ)≤(M:ℝ)^d) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N in atTop,
      (chenLowerMainCoeff θ-ε)*(twinChenU N (r N)/Real.log (N:ℝ))≤chenAPLowerPolynomial θ N (2*r N) ∧
      chenAPMediumPolynomial θ N (2*r N)≤(chenMediumMainCoeff θ+ε)*(twinChenU N (r N)/Real.log (N:ℝ)) ∧
      chenAPSwitchedPolynomial θ N (2*r N)≤(2/θ+ε)*(twinChenU N (r N)/Real.log (N:ℝ)) := by
  let V (a : ℝ) (N : ℕ) := chenDensityProduct (2*r N) (chenPowerLevel a N)*Real.log (N:ℝ)/twinChenU N (r N)
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
  have hV (a : ℝ) (ha : d<a) (ha₁ : a≤1) : Tendsto (V a) atTop (𝓝 (K a)) :=
    twinChen_density_log_tendsto hd₀ ha ha₁ r hr
  have hθp : 0<θ := by linarith
  have hL : ContinuousAt linearSieveLowerFactor (8*θ) := by
    unfold linearSieveLowerFactor
    fun_prop (disch := intro he; linarith)
  have hU : ContinuousAt linearSieveUpperFactor (3*θ) := by
    unfold linearSieveUpperFactor
    fun_prop (disch := positivity)
  have hsz := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/8))
  have hsy := (chenSieveParameter_tendsto hθp (by norm_num : (0:ℝ)<1/3))
  rw [show θ/(1/8)=8*θ by ring] at hsz
  rw [show θ/(1/3)=3*θ by ring] at hsy
  have hFz := (hV (1/8) hd (by norm_num)).mul
    ((hL.tendsto.comp hsz).sub_const δ)
  have hFy := (hV (1/3) (by linarith only [hd]) (by norm_num)).mul
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
  have hC : Tendsto chenAPMediumScale atTop (𝓝 c) :=
    ((chenLogPowerLevel_tendsto (by norm_num : (0:ℝ)<1/8))).const_mul _
  have hm : Tendsto twinChenMediumMass atTop (𝓝 J) := twinChenMediumMass_tendsto
  have hi : Tendsto (twinChenMediumIdeal θ) atTop (𝓝 (chenMediumMainCoeff θ)) :=
    (twinChenMediumIdeal_tendsto (by linarith : 1/3<θ))
  have hmed := (hV (1/8) hd (by norm_num)).mul
    ((hC.mul hi).add (((hC.add_const 1).const_mul δ).mul hm))
  have hKc : K (1/8)*c=1 := by dsimp [K,c]; rw [Real.exp_neg]; field_simp
  have hmc : K (1/8)*(c*chenMediumMainCoeff θ+δ*(c+1)*J) =
      chenMediumMainCoeff θ+δ*A := by
    dsimp only [A]; linear_combination (chenMediumMainCoeff θ)*hKc
  have hmid := hmed.eventually (Iio_mem_nhds (show K (1/8)*(c*chenMediumMainCoeff θ+δ*(c+1)*J)<
      chenMediumMainCoeff θ+ε by rw [hmc]; linarith only [hAδ]))
  filter_upwards [hlo,hmid,hsw,chenAP_floor_profiles hθ hθ₂ hδ,
    chenActualSieveParameters_eventually_mem hθ hθ₂,chenMediumReciprocalFloor_eventually_le hθ hδ,
    eventually_ge_atTop (2^24:ℕ)] with N hlo hmid hsw hp hparams hfloor hN
  let m := 2*r N
  let L := Real.log (N:ℝ)
  let U := twinChenU N (r N)
  have hn₂ : 2≤N := by omega
  have hem : Even m := even_two_mul _
  have hpos := twinChenU_ge_half hn₂ (r N)
  have hu : 0<U := by dsimp [U]; linarith only [hpos]
  have hNr : (2:ℝ)≤N := by exact_mod_cast hn₂
  have hl : 0<L := Real.log_pos (by linarith)
  have hscale : 0≤U/L := div_nonneg hu.le hl.le
  have hcancel (a F : ℝ) : (V a N*F)*(U/L)=chenDensityProduct m (chenPowerLevel a N)*F := by
    change (chenDensityProduct m _*L/U*F)*(U/L)=_
    field_simp
  obtain ⟨hpl,hps,hpm⟩ := hp m hem
  have h₁ := mul_le_mul_of_nonneg_right (le_of_lt hlo) hscale
  have h₂ := mul_le_mul_of_nonneg_right (le_of_lt hmid) hscale
  have h₃ := mul_le_mul_of_nonneg_right (le_of_lt hsw) hscale
  refine ⟨h₁.trans ((hcancel (1/8) _).le.trans hpl),?_,hps.trans ((hcancel (1/3) _).ge.trans h₃)⟩
  exact (twinChen_medium_envelope hθ hδ.le hN hpm
    (fun q hq => (hparams.2.2 q hq).1) hfloor).trans ((hcancel (1/8) _).ge.trans h₂)

/-- The three sieve polynomials have a common source-size normalization.
The starting point is uniform in every auxiliary modulus in the stated range. -/
theorem twinChenRosserMainComparisons_unconditional {δ θ : ℝ}
    (hδ₀ : 0≤δ) (hδ : δ<1/8) (hθ₁ : 11/24<θ) (hθ₂ : θ<1/2) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ M : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ →
      (chenLowerMainCoeff θ-ε)*(twinChenU M r/Real.log (M:ℝ))≤chenAPLowerPolynomial θ M (2*r) ∧
      chenAPMediumPolynomial θ M (2*r)≤(chenMediumMainCoeff θ+ε)*(twinChenU M r/Real.log (M:ℝ)) ∧
      chenAPSwitchedPolynomial θ M (2*r)≤(2/θ+ε)*(twinChenU M r/Real.log (M:ℝ)) := by
  classical
  intro ε hε
  let P (M r : ℕ) : Prop :=
    (chenLowerMainCoeff θ-ε)*(twinChenU M r/Real.log (M:ℝ))≤chenAPLowerPolynomial θ M (2*r) ∧
    chenAPMediumPolynomial θ M (2*r)≤(chenMediumMainCoeff θ+ε)*(twinChenU M r/Real.log (M:ℝ)) ∧
    chenAPSwitchedPolynomial θ M (2*r)≤(2/θ+ε)*(twinChenU M r/Real.log (M:ℝ))
  let r (M : ℕ) := if h : ∃ k : ℕ, 0<k ∧ (k:ℝ)≤(M:ℝ)^δ ∧ ¬P M k then h.choose else 1
  have hr (M : ℕ) (hM : 1≤M) : 0<r M ∧ (r M:ℝ)≤(M:ℝ)^δ := by
    dsimp only [r]
    split_ifs with h
    · exact ⟨h.choose_spec.1,h.choose_spec.2.1⟩
    · refine ⟨by decide,?_⟩
      simpa only [Nat.cast_one] using Real.one_le_rpow (Nat.one_le_cast.mpr hM) hδ₀
  filter_upwards [twin_comparisons_along hδ₀ hδ hθ₁ hθ₂ r hr hε] with M h k hk hkM
  change P M k
  by_contra hb
  have ht : ∃ j : ℕ, 0<j ∧ (j:ℝ)≤(M:ℝ)^δ ∧ ¬P M j := ⟨k,hk,hkM,hb⟩
  have hg : P M (r M) := h
  exact ht.choose_spec.2.2 (by simpa only [r,dite_eq_left ht] using hg)

/-- Every medium prime is larger than the full auxiliary modulus. -/
theorem twinChen_medium_not_dvd {δ : ℝ} (hδ₀ : 0≤δ) (hδ : δ<1/8) :
    ∀ᶠ M : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(M:ℝ)^δ →
      ∀ q∈chenMediumPrimes (chenLowerCutoff M) (chenUpperCutoff M), ¬q∣2*r := by
  filter_upwards [twinChen_modulus_lt_cutoff hδ₀ hδ] with M hcut r hr hrM q hq hd
  have hqz := (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1
  exact ((hcut r hrM).trans_le hqz).not_ge (Nat.le_of_dvd (by positivity) hd)

end FareyGoldbach

