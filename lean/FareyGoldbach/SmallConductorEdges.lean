import FareyGoldbach.SmallConductorKernel
import FareyGoldbach.SmoothedExplicitFormula

/-! # Error bounds for a sharp Perron rectangle at small conductor -/

open Set MeasureTheory
open scoped Interval Classical

namespace FareyGoldbach

private theorem norm_normalized_right_sub_residue {bot top left right res : ℂ}
    (h : bot-top+Complex.I*right-Complex.I*left=2*(Real.pi:ℂ)*Complex.I*res) :
    ‖(2*(Real.pi:ℂ))⁻¹*right-res‖≤‖left‖+‖bot‖+‖top‖ := by
  let A := 2*(Real.pi:ℂ)
  have ha : A≠0 := mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have haI := mul_ne_zero ha Complex.I_ne_zero
  have hdiv := congrArg (fun z => (A*Complex.I)⁻¹*z) h
  change (A*Complex.I)⁻¹*(bot-top+Complex.I*right-Complex.I*left)=(A*Complex.I)⁻¹*(A*Complex.I*res) at hdiv
  have hc : (A*Complex.I)⁻¹*Complex.I = A⁻¹ := by field_simp [ha,Complex.I_ne_zero]
  rw [inv_mul_cancel_left₀ haI,mul_sub,mul_add,←mul_assoc,←mul_assoc,hc] at hdiv
  have he : A⁻¹*right-res=A⁻¹*left-(A*Complex.I)⁻¹*(bot-top) := by linear_combination hdiv
  have hco : ‖A⁻¹‖≤1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    simp only [A,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    linarith only [Real.pi_gt_three]
  have hco' : ‖(A*Complex.I)⁻¹‖≤1 := by simpa [norm_inv,norm_mul] using hco
  change ‖A⁻¹*right-res‖≤_
  rw [he]
  calc
    _ ≤ ‖A⁻¹*left‖+‖(A*Complex.I)⁻¹*(bot-top)‖ := norm_sub_le _ _
    _ ≤ ‖left‖+‖bot-top‖ := by
      simp only [norm_mul]
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hco)
        (mul_le_of_le_one_left (norm_nonneg _) hco')
    _ ≤ _ := by linarith only [norm_sub_le bot top]

set_option maxHeartbeats 800000 in
/-- The left edge uses the uniform multiplier bound. On each horizontal edge
the product gains three powers of the height from the twice-averaged cutoff. -/
theorem smallConductorRectangle_edge_bounds {X d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {δ η β T M : ℝ} (hX : 2≤X) (hδ : 0<δ) (hδ1 : δ≤1) (hη : 0<η) (hη1 : η≤1/4)
    (hβ : 1<β) (hβ2 : β≤2) (hT : 1≤T) (hM : 0≤M)
    (hid : rectIntegral (fun s => smallConductorKernel X δ s*negLogDerivL χ s) (1-η) β (-T) T =
      2*(Real.pi:ℂ)*Complex.I*(if χ=1 then smallConductorKernel X δ 1 else 0))
    (hl : ∀ t∈Icc (-T) T, ‖negLogDerivL χ (((1-η:ℝ):ℂ)+(t:ℂ)*Complex.I)‖≤M)
    (hh : ∀ x∈Icc (1-η) β, ∀ t : ℝ, |t|=T →
      ‖negLogDerivL χ ((x:ℂ)+(t:ℂ)*Complex.I)‖≤M) :
    ‖(2*(Real.pi:ℂ))⁻¹*(∫ t in -T..T, smallConductorKernel X δ ((β:ℂ)+(t:ℂ)*Complex.I)*
      negLogDerivL χ ((β:ℂ)+(t:ℂ)*Complex.I))-
      (if χ=1 then smallConductorKernel X δ 1 else 0)‖ ≤
      50000*((X:ℝ)^(1-η)*M*T+(X:ℝ)^β*M/(δ^2*T^3)) := by
  let a := 1-η
  let f : ℂ→ℂ := fun s => smallConductorKernel X δ s*negLogDerivL χ s
  have ha₄ : 1/4≤a := by dsimp [a]; linarith only [hη1]
  have ha : 0<a := by linarith only [ha₄]
  have ha₁ : a<1 := by dsimp [a]; linarith
  have hab := ha₁.trans hβ
  have hT₀ := zero_lt_one.trans_le hT
  have ht : -T≤T := by linarith
  have hx : 0<X := by omega
  have hx₁ : (1:ℝ)≤X := Nat.one_le_cast.mpr hx
  let V := (X:ℝ)^a*M
  let W := (X:ℝ)^β*M/(δ^2*T^3)
  have hV : 0≤V := by dsimp [V]; positivity
  have hW : 0≤W := by dsimp [W]; positivity
  have hkernel (x t : ℝ) (hx₄ : 1/4≤x) (hx₂ : x≤2) :
      ‖sharpPerronKernel δ ((x:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        12500*min (1/(1+|t|)) (1/(δ^2*(1+|t|)^3)) := by
    simpa using sharpPerronKernel_norm_le_min_height hδ hδ1
      (s:=(x:ℂ)+(t:ℂ)*Complex.I) (by simpa using hx₄) (by simpa using hx₂)
  have hleft (t : ℝ) (ht' : t∈Icc (-T) T) :
      ‖f ((a:ℂ)+(t:ℂ)*Complex.I)‖≤12500*V := by
    have hk := (hkernel a t ha₄ (hab.le.trans hβ2)).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
    have hh₁ : 1/(1+|t|)≤1 := (div_le_one (by positivity)).mpr (by linarith [abs_nonneg t])
    have hkk : ‖sharpPerronKernel δ ((a:ℂ)+(t:ℂ)*Complex.I)‖≤12500 := by
      linarith only [hk,hh₁]
    simp only [f,norm_mul,norm_smallConductorKernel hx,
      show ((a:ℂ)+(t:ℂ)*Complex.I).re=a by simp]
    calc
      _ ≤ ((X:ℝ)^a*12500)*M := mul_le_mul (mul_le_mul_of_nonneg_left hkk (by positivity))
        (hl t ht') (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [V]; ring
  have hhor (x t : ℝ) (hx' : x∈Icc a β) (htt : |t|=T) :
      ‖f ((x:ℂ)+(t:ℂ)*Complex.I)‖≤12500*W := by
    have hk := (hkernel x t (ha₄.trans hx'.1) (hx'.2.trans hβ2)).trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num))
    rw [htt] at hk
    have hdiv : 1/(δ^2*(1+T)^3)≤1/(δ^2*T^3) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hT₀.le (by linarith : T≤1+T) 3) (sq_nonneg δ)
    have hkk := hk.trans (mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ)≤12500))
    simp only [f,norm_mul,norm_smallConductorKernel hx,
      show ((x:ℂ)+(t:ℂ)*Complex.I).re=x by simp]
    calc
      _ ≤ ((X:ℝ)^β*(12500*(1/(δ^2*T^3))))*M := mul_le_mul
        (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx₁ hx'.2) hkk (norm_nonneg _) (by positivity))
        (hh x hx' t htt) (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [W]; ring
  have hbnd (t : ℝ) (htt : |t|=T) :
      ‖∫ x in a..β, f ((x:ℂ)+(t:ℂ)*Complex.I)‖≤25000*W := by
    have h₀ := intervalIntegral.norm_integral_le_of_norm_le_const (a:=a) (b:=β)
      (fun x hx' => hhor x t (by rw [uIoc_of_le hab.le] at hx'; exact ⟨hx'.1.le,hx'.2⟩) htt)
    rw [abs_of_nonneg (sub_nonneg.mpr hab.le)] at h₀
    have hwidth : β-a≤2 := by linarith only [hβ2,ha]
    linarith only [h₀,mul_le_mul_of_nonneg_left hwidth (by positivity : 0≤12500*W)]
  have hvb : ‖∫ t in -T..T, f ((a:ℂ)+(t:ℂ)*Complex.I)‖≤25000*V*T := by
    have h₀ := intervalIntegral.norm_integral_le_of_norm_le_const (a:=-T) (b:=T)
      (fun t ht' => hleft t (by rw [uIoc_of_le ht] at ht'; exact ⟨ht'.1.le,ht'.2⟩))
    rw [abs_of_nonneg (sub_nonneg.mpr ht)] at h₀
    linarith only [h₀]
  have hnorm := norm_normalized_right_sub_residue hid
  change ‖(2*(Real.pi:ℂ))⁻¹*(∫ t in -T..T, f ((β:ℂ)+(t:ℂ)*Complex.I))-
    (if χ=1 then smallConductorKernel X δ 1 else 0)‖≤50000*(V*T+W)
  refine hnorm.trans ?_
  have hn := hbnd (-T) (by rw [abs_neg,abs_of_nonneg hT₀.le])
  have hp := hbnd T (abs_of_nonneg hT₀.le)
  linarith only [hvb,hn,hp,mul_nonneg hV hT₀.le]

end FareyGoldbach
