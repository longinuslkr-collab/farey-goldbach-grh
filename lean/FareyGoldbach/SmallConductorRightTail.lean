import FareyGoldbach.SmallConductorPerron
import FareyGoldbach.SmoothedExplicitFormula

/-! # The right-hand tails of the small-conductor Perron integral -/

open Complex Set MeasureTheory
open scoped Interval

namespace FareyGoldbach

private theorem inverse_cube_integral_bound {g : ℝ → ℂ} (hg : Integrable g) {T A : ℝ}
    (hT : 0<T) (hbound : ∀ u>T, ‖g u‖≤A*u^(-3:ℝ)) :
    ‖∫ u in Ioi T, g u‖ ≤ A/(2*T^2) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ)< -1) hT
  calc
    _ ≤ ∫ u in Ioi T, ‖g u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi T, A*u^(-3:ℝ) :=
      setIntegral_mono_on hg.norm.integrableOn (hi.const_mul _) measurableSet_Ioi (fun u hu => hbound u hu)
    _ = _ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ)< -1) hT]
      norm_num [Real.rpow_neg hT.le]
      ring

/-- The full integral on the line Re s = σ differs from its truncation at
heights ±T by an explicit inverse-square tail. -/
theorem norm_smallConductor_right_tail {X q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hX : 0<X) {δ σ T M : ℝ} (hδ : 0<δ) (hδ₁ : δ≤1) (hσ : 1<σ) (hσ₂ : σ≤2)
    (hT : 1≤T) (hM : 0≤M)
    (hbd : ∀ t : ℝ, ‖negLogDerivL χ ((σ:ℂ)+(t:ℂ)*I)‖≤M) :
    ‖(2*(Real.pi:ℂ))⁻¹*(∫ t : ℝ,
        smallConductorKernel X δ ((σ:ℂ)+(t:ℂ)*I)*negLogDerivL χ ((σ:ℂ)+(t:ℂ)*I)) -
      (2*(Real.pi:ℂ))⁻¹*(∫ t in -T..T,
        smallConductorKernel X δ ((σ:ℂ)+(t:ℂ)*I)*negLogDerivL χ ((σ:ℂ)+(t:ℂ)*I))‖ ≤
        12500*(X:ℝ)^σ*M/(δ^2*T^2) := by
  let s (u : ℝ) : ℂ := (σ:ℂ)+(u:ℂ)*I
  let K (u : ℝ) := smallConductorKernel X δ (s u)
  let F (u : ℝ) := K u*negLogDerivL χ (s u)
  let A := 12500*(X:ℝ)^σ*M/δ^2
  have ht := zero_lt_one.trans_le hT
  have hx : 0<(X:ℝ) := Nat.cast_pos.mpr hX
  have hsre (u : ℝ) : (s u).re=σ := by simp [s]
  have hsim (u : ℝ) : (s u).im=u := by simp [s]
  have hsne (u : ℝ) : s u≠1 := fun he => by
    have hh := congrArg Complex.re he
    rw [hsre,Complex.one_re] at hh
    linarith only [hh,hσ]
  have hcont : Continuous (fun u : ℝ => negLogDerivL χ (s u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    have hne := χ.LFunction_ne_zero_of_one_le_re (.inr (hsne u)) (by simpa only [hsre] using hσ.le)
    have hent : entireL χ (s u)≠0 := by
      rw [entireL_apply_of_ne_one χ (hsne u)]
      split <;> first | exact mul_ne_zero (sub_ne_zero.mpr (hsne u)) hne | exact hne
    exact (continuousAt_negLogDerivL χ (hsne u) hent).comp (by dsimp [s]; fun_prop)
  have hK : Integrable K := smallConductorKernel_vertical_integrable hX hδ hδ₁ (by linarith only [hσ]) hσ₂
  have hF : Integrable F := by
    exact hK.mul_bdd hcont.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hpoint (u : ℝ) (hu : 0 < |u|) : ‖F u‖ ≤ A*|u|^(-3:ℝ) := by
    have hker := sharpPerronKernel_norm_le_min_height hδ hδ₁ (s:=s u)
      (by rw [hsre]; linarith only [hσ]) (by simpa only [hsre] using hσ₂)
    rw [hsim] at hker
    have hker' := hker.trans (mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num))
    have hd3 : δ^2*|u|^3 ≤ δ^2*(1+|u|)^3 := by gcongr; linarith
    have H := hker'.trans (mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le (by positivity) hd3) (by norm_num))
    calc
      _ = ((X:ℝ)^σ*‖sharpPerronKernel δ (s u)‖)*‖negLogDerivL χ (s u)‖ := by
        dsimp only [F,K]
        rw [norm_mul,norm_smallConductorKernel hX,hsre]
      _ ≤ ((X:ℝ)^σ*(12500*(1/(δ^2*|u|^3))))*M := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left H (by positivity)) (hbd u) (norm_nonneg _) (by positivity)
      _ = _ := by
        dsimp only [A]
        rw [Real.rpow_neg hu.le,show (3:ℝ)=((3:ℕ):ℝ) from rfl,Real.rpow_natCast]
        ring
  have hpos := inverse_cube_integral_bound hF ht (A:=A) (fun u hu => by
    simpa only [abs_of_pos (ht.trans hu)] using hpoint u (abs_pos.mpr (ht.trans hu).ne'))
  have hneg := inverse_cube_integral_bound hF.comp_neg ht (A:=A) (fun u hu => by
    have hp : 0 < |-u| := by rw [abs_neg,abs_of_pos (ht.trans hu)]; exact ht.trans hu
    simpa only [abs_neg,abs_of_pos (ht.trans hu)] using hpoint (-u) hp)
  rw [integral_comp_neg_Ioi] at hneg
  have hle : -T≤T := by linarith only [ht]
  have hwhole := integral_add_compl (f:=F) (s:=Iic (-T)) measurableSet_Iic hF
  rw [compl_Iic] at hwhole
  have hmid := intervalIntegral.integral_Ioi_sub_Ioi (f:=F) (hF.integrableOn (s:=Ioi (-T))) hle
  have hsplit : (∫ u : ℝ, F u) - (∫ u in -T..T, F u) =
      (∫ u in Iic (-T), F u) + ∫ u in Ioi T, F u := by
    rw [← hwhole,← hmid]
    abel
  have hpi : ‖(2*(Real.pi:ℂ))⁻¹‖≤1 := by
    have he : 1≤‖(2:ℂ)*(Real.pi:ℂ)‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
      norm_num
      linarith only [Real.pi_gt_three]
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le he)).mpr he
  change ‖(2*(Real.pi:ℂ))⁻¹*(∫ u : ℝ,F u) - (2*(Real.pi:ℂ))⁻¹*(∫ u in -T..T,F u)‖≤_
  rw [←mul_sub,hsplit,norm_mul]
  have hA : 0≤A :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg X) σ)) hM)
      (sq_nonneg δ)
  calc
    _ ≤ ‖(2*(Real.pi:ℂ))⁻¹‖*(A/(2*T^2)+A/(2*T^2)) := mul_le_mul_of_nonneg_left
      ((norm_add_le ..).trans (add_le_add hneg hpos)) (norm_nonneg _)
    _ ≤ 1*(A/(2*T^2)+A/(2*T^2)) := mul_le_mul_of_nonneg_right hpi (by positivity)
    _ = _ := by dsimp [A]; ring

end FareyGoldbach
