import FareyGoldbach.ChenAPSmallConductor

/-! # GRH cancellation on the last-prime fibers of the switching carrier -/

namespace FareyGoldbach

/-- The unrestricted switching mass uses the masked box estimate at mask one. -/
theorem chenAP_switching_box_twist_of_dirichletGRH (hGRH : DirichletGRH) :
    ∃ C : ℝ, 0<C ∧ ∀ {N z y i r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r),
      0<N → r≤N → (N:ℝ)^(1/4:ℝ)+1≤(y:ℝ) → χ≠1 →
      ‖chenSwitchBoxSum N z y i 1 χ‖≤C*(N:ℝ)^(7/8:ℝ)*(chenSwitchLog N)^2 := by
  obtain ⟨C,hC,h⟩ := chen_ap_switch_box_twist_of_dirichletGRH hGRH
  refine ⟨C,hC,?_⟩
  intro N z y i r _ χ hN hrN hy hχ
  have hq : 1<r := by
    by_contra! hr
    have h₁ := Nat.le_antisymm hr (NeZero.pos r)
    have hd : χ.conductor∣1 := χ.conductor_dvd_level.trans (by rw [h₁])
    exact hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr (Nat.dvd_one.mp hd))
  have hNN : N≤N^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_left _ hN
  exact h χ hN hy le_rfl ((show 1≤N from hN).trans hNN) hq (hrN.trans hNN) hχ

end FareyGoldbach
