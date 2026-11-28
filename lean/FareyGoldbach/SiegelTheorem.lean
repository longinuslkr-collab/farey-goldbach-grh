import FareyGoldbach.SiegelProducts
import FareyGoldbach.SiegelExceptional
import FareyGoldbach.SiegelRealGap

/-! # Siegel's lower bound and the real-zero gap -/

open Complex Set
open scoped Classical

namespace FareyGoldbach

/- The reference character, when needed, is chosen once for ε. In the other
case the two-factor product at a fixed β suffices for every character. -/
theorem siegel_L_one_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 1 < q → χ^2 = 1 → c*(q:ℝ)^(-ε) ≤ ‖χ.LFunction 1‖ := by
  obtain ⟨C,hC,hTwo,hFour⟩ := siegel_estermann_residue_bounds
  obtain ⟨ρ,hρ,hzeta⟩ := riemannZeta_re_neg_left_near_one
  let u := ε/2
  have hu : 0 < u := by dsimp only [u]; positivity
  let δ := min (1/8:ℝ) (min (ρ/2) (u/C))
  have hδ : 0<δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ₁ : δ≤1/8 := min_le_left ..
  have hδ₂ : δ≤ρ/2 := (min_le_right ..).trans (min_le_left ..)
  have hδ₃ : C*δ≤u := by
    rw [mul_comm]
    apply (le_div_iff₀ hC).mp
    exact (min_le_right (1/8:ℝ) _).trans (min_le_right (ρ/2) (u/C))
  have hβs (β : ℝ) (hβ : 1-δ≤β) : 7/8≤β ∧ C*(1-β)≤u := by
    refine ⟨by linarith only [hβ,hδ₁],?_⟩
    exact (mul_le_mul_of_nonneg_left (by linarith only [hβ]) hC.le).trans hδ₃
  by_cases hRef : ∃ (q₁ : ℕ) (hq₁ : 1<q₁) (χ₁ : DirichletCharacter ℂ q₁) (β : ℝ),
      let _ : NeZero q₁ := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq₁)⟩
      χ₁.IsPrimitive ∧ χ₁^2=1 ∧ 1-δ≤β ∧ β<1 ∧ χ₁.LFunction (β:ℂ)=0
  · obtain ⟨q₁,hq₁,χ₁,β,hprim₁,hquad₁,hβ,hβ',hzero⟩ := hRef
    let _ : NeZero q₁ := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq₁)⟩
    have ⟨hβ₀,hβu⟩ := hβs β hβ
    exact siegel_lower_of_reference_zero hε hβ₀ hβ' hβu hprim₁ hq₁ hquad₁ hzero hFour
  · let β := 1-δ
    have hβ' : β<1 := sub_lt_self _ hδ
    have ⟨hβ₀,hβu⟩ := hβs β le_rfl
    have hz : (riemannZeta (β:ℂ)).re<0 :=
      hzeta β (by dsimp only [β]; linarith only [hδ₂,hρ]) hβ'
    refine ⟨(δ/2)*(2:ℝ)^(-ε),by positivity,?_⟩
    intro q _ χ hprim hq hquad
    have hχ : χ≠1 := fun he => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim he)
    have he (x : ℝ) (hx : x∈Ico β 1) : χ.LFunction (x:ℂ)≠0 := by
      intro hzero
      exact hRef ⟨q,hq,χ,x,hprim,hquad,hx.1,hx.2,hzero⟩
    have hn := quadratic_LFunction_re_nonneg_of_zero_free_interval hquad hχ hβ' he
    have hf : (riemannZeta (β:ℂ)*χ.LFunction (β:ℂ)).re≤0 := by
      rw [Complex.mul_re,quadratic_LFunction_im_eq_zero hquad hχ β,mul_zero,sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hz.le hn
    have hQ : 1≤2*(q:ℝ) := by
      have hqR : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.le
      linarith only [hqR]
    have hcomp : -ε≤ -(C*(1-β)) := by dsimp only [u] at hβu; linarith only [hε,hβu]
    have hgap : 1-β=δ := by dsimp only [β]; ring
    calc
      _ = (1-β)/2*(2*(q:ℝ))^(-ε) := by
        rw [hgap,Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Nat.cast_nonneg _)]
        ring
      _ ≤ (1-β)/2*(2*(q:ℝ))^(-(C*(1-β))) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hQ hcomp) (by positivity)
      _ ≤ _ := hTwo q χ hχ hquad β hβ₀ hβ' hf

/-- The closed real interval in Siegel's gap contains no real zero. -/
theorem siegel_real_zero_gap (ε : ℝ) (hε : 0<ε) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 1<q → χ^2=1 → ∀ β : ℝ,
        1-c*(q:ℝ)^(-ε)≤β → β<1 → χ.LFunction (β:ℂ)≠0 :=
  siegel_real_zero_gap_of_L_one_lower siegel_L_one_lower ε hε

end FareyGoldbach
