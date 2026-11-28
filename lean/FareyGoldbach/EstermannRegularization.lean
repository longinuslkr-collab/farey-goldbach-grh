import FareyGoldbach.EstermannTaylor
import FareyGoldbach.LocalLogDerivative

/-! # Estermann's residue estimate for a product with the Riemann zeta function -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem estermann_disk_re_norm {s : ℂ} (hs : s∈Metric.closedBall 2 (3/2:ℝ)) :
    1/2≤s.re ∧ ‖s‖≤4 := by
  have hd := Metric.mem_closedBall.mp hs
  rw [dist_eq_norm] at hd
  have hre := (abs_le.mp ((Complex.abs_re_le_norm (s-2)).trans hd)).1
  have hn := norm_add_le (s-2) (2:ℂ)
  rw [sub_add_cancel] at hn
  norm_num at hre hn
  constructor <;> linarith

open scoped ComplexOrder in
/-- An entire numerator makes the principal part of a zeta product explicit.
The universal constant depends only on the fixed disk and its zeta factor. -/
theorem estermann_zeta_product_residue_lower :
    ∃ C : ℝ, 0<C ∧ ∀ {Q : ℕ} {P : ℂ→ℂ} {a : ℕ→ℂ} {res β : ℝ},
      1≤Q → Differentiable ℂ P →
      (∀ s∈Metric.closedBall (2:ℂ) (3/2:ℝ), ‖P s‖≤64^3*(Q:ℝ)^3) →
      P 1=(res:ℂ) → 0≤res → (∀ n,0≤a n) → a 1=1 →
      (∀ s : ℂ, 1<s.re → LSeriesSummable a s) →
      (∀ s : ℂ, 1<s.re → riemannZeta s*P s=LSeries a s) →
      7/8≤β → β<1 → (riemannZeta β*P β).re≤0 →
      (1-β)/2*(2*(Q:ℝ))^(-(C*(1-β)))≤res := by
  classical
  let Z := entireL (1 : DirichletCharacter ℂ 1)
  have hZ : Differentiable ℂ Z := differentiable_entireL _
  obtain ⟨M,hM⟩ := (isCompact_closedBall (2:ℂ) (3/2:ℝ)).exists_bound_of_continuousOn
    hZ.continuous.continuousOn
  let B : ℝ := max M 1*64^3
  have hB : 0<B := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right M 1)) (by norm_num)
  obtain ⟨C,hC,hTaylor⟩ := estermann_lseries_lower (4*B) (by positivity)
  refine ⟨C,hC,?_⟩
  intro Q P a res β hQ hP hPbound hres₁ hres ha ha₁ hsum hseries hβ hβ' hn
  let F : ℂ→ℂ := fun s => riemannZeta s*P s
  let H : ℂ→ℂ := fun s => Z s*P s
  let G := dslope H 1
  have hHd : Differentiable ℂ H := hZ.mul hP
  have hG : Differentiable ℂ G := fun s => ((hHd.analyticAt s).dslope 1).differentiableAt
  have hH₁ : H 1=(res:ℂ) := by
    simpa [H,Z,entireL,DirichletCharacter.LFunctionTrivChar₁] using hres₁
  have hH (s : ℂ) (hs : s≠1) : H s=(s-1)*F s := by
    simp [H,Z,entireL_apply_of_ne_one _ hs,DirichletCharacter.LFunction_modOne_eq,F,mul_assoc]
  have hquot (s : ℂ) (hs : s≠1) : G s=(H s-H 1)/(s-1) :=
    (dslope_of_ne H hs).trans (slope_def_field H 1 s)
  have hregular (s : ℂ) (hs : s≠1) : F s=G s+(res:ℂ)/(s-1) := by
    rw [hquot s hs,hH₁,hH s hs,←add_div,sub_add_cancel]
    exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs)).symm
  have hbound (s : ℂ) (hs : s∈Metric.closedBall 2 (3/2:ℝ)) : ‖H s‖≤B*(Q:ℝ)^3 := by
    calc
      ‖H s‖ = ‖Z s‖*‖P s‖ := norm_mul _ _
      _ ≤ max M 1*(64^3*(Q:ℝ)^3) := mul_le_mul ((hM s hs).trans (le_max_left _ _))
        (hPbound s hs) (norm_nonneg _) ((norm_nonneg _).trans ((hM s hs).trans (le_max_left _ _)))
      _ = B*(Q:ℝ)^3 := by dsimp [B]; ring
  have hdist₁₂ : dist (1:ℂ) 2=1 := by norm_num [dist_eq_norm]
  have h₁cl : (1:ℂ)∈Metric.closedBall 2 (3/2:ℝ) := by
    rw [Metric.mem_closedBall,hdist₁₂]; norm_num
  have hGbound (s : ℂ) (hs : s∈Metric.sphere 2 (3/2:ℝ)) : ‖G s‖≤4*B*(Q:ℝ)^10 := by
    have ht := dist_triangle s 1 (2:ℂ)
    rw [Metric.mem_sphere.mp hs,hdist₁₂,dist_eq_norm] at ht
    have hden : (1/2:ℝ)≤‖s-1‖ := by linarith
    have hne : s≠1 := by
      rintro rfl
      norm_num at hden
    have hsum := (norm_sub_le (H s) (H 1)).trans
      (add_le_add (hbound s (Metric.sphere_subset_closedBall hs)) (hbound 1 h₁cl))
    calc
      ‖G s‖ = ‖H s-H 1‖/‖s-1‖ := by rw [hquot s hne,norm_div]
      _ ≤ (B*(Q:ℝ)^3+B*(Q:ℝ)^3)/(1/2) :=
        div_le_div₀ (by positivity) hsum (by norm_num) hden
      _ = 4*B*(Q:ℝ)^3 := by ring
      _ ≤ 4*B*(Q:ℝ)^10 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by exact_mod_cast hQ) (by norm_num)) (by positivity)
  have hβne : (β:ℂ)≠1 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re,Complex.one_re] at hre
    exact hβ'.ne hre
  have hnear : ∀ᶠ s : ℂ in 𝓝 2, 1<s.re := (isOpen_lt continuous_const
    Complex.continuous_re).mem_nhds (by norm_num : 1<(2:ℂ).re)
  have h := hTaylor (F:=F) hQ hres hβ hβ' hG.diffContOnCl hGbound
    ((eventually_ne_nhds (by norm_num : (2:ℂ)≠1)).mono hregular)
    (hregular β hβne) ha ha₁ hsum (hnear.mono hseries)
  exact estermann_residue_lower_of_nonpos hQ hβ' hn h

end FareyGoldbach
