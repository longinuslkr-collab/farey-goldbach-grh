import FareyGoldbach.EstermannRegularization
import FareyGoldbach.SiegelLocal
import FareyGoldbach.SiegelLValues

/-! # Two-factor and four-factor applications of the Estermann estimate -/

open Complex Metric
open scoped ComplexOrder

namespace FareyGoldbach

private theorem norm_LFunction_estermann_disk {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ}
    (hs : s ∈ closedBall (2 : ℂ) (3/2 : ℝ)) :
    ‖χ.LFunction s‖ ≤ 64*(q:ℝ) := by
  have ⟨hre,hnorm⟩ := estermann_disk_re_norm hs
  calc
    _ ≤ 16*(q:ℝ)*‖s‖ := norm_LFunction_le_of_ne_one χ hχ (by linarith only [hre])
    _ ≤ 16*(q:ℝ)*4 := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

/-- The same absolute truncation exponent can be used in the two-factor
argument and with a fixed real zero of a character in the four-factor product. -/
theorem siegel_estermann_residue_bounds :
    ∃ C : ℝ, 0 < C ∧
      (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ ≠ 1 → χ^2 = 1 → ∀ β : ℝ, 7/8≤β → β<1 →
        (riemannZeta (β:ℂ) * χ.LFunction (β:ℂ)).re ≤ 0 →
        (1-β)/2 * (2*(q:ℝ))^(-(C*(1-β))) ≤ ‖χ.LFunction 1‖) ∧
      (∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q),
        χ ≠ 1 → ψ ≠ 1 → χ*ψ ≠ 1 → χ^2 = 1 → ψ^2 = 1 →
        ∀ β : ℝ, 7/8≤β → β<1 → χ.LFunction (β:ℂ) = 0 →
        (1-β)/2 * (2*(q:ℝ))^(-(C*(1-β))) ≤
          ‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(χ*ψ).LFunction 1‖) := by
  obtain ⟨C,hC,H⟩ := estermann_zeta_product_residue_lower
  refine ⟨C,hC,?_,?_⟩
  · intro q _ χ hn hχ β hβ hβ' hF
    have hq : (1:ℝ)≤q := Nat.one_le_cast.mpr (NeZero.pos q)
    apply H (Q:=q) (P:=χ.LFunction) (a:=χ.zetaMul) (NeZero.pos q)
      (χ.differentiable_LFunction hn) _ (quadratic_LFunction_one_eq_norm hχ hn)
      (norm_nonneg _) (DirichletCharacter.zetaMul_nonneg hχ) χ.isMultiplicative_zetaMul.map_one
      (fun _ hs => χ.LSeriesSummable_zetaMul hs)
      (fun _ hs => (estermannTwo_LSeries_eq χ hs).symm) hβ hβ' hF
    intro s hs
    calc
      _ ≤ 64*(q:ℝ) := norm_LFunction_estermann_disk χ hn hs
      _ ≤ (64*(q:ℝ))^3 := le_self_pow₀ (by linarith only [hq]) (by norm_num)
      _ = _ := by ring
  · intro q _ χ ψ hχ₀ hψ₀ hprod hχ hψ β hβ hβ' hzero
    let P : ℂ → ℂ := fun s => χ.LFunction s * ψ.LFunction s * (χ*ψ).LFunction s
    have hpq : (χ*ψ)^2=1 := by rw [mul_pow,hχ,hψ,one_mul]
    have hP : Differentiable ℂ P := ((χ.differentiable_LFunction hχ₀).mul
      (ψ.differentiable_LFunction hψ₀)).mul ((χ*ψ).differentiable_LFunction hprod)
    have hres : P 1 = ((‖χ.LFunction 1‖ * ‖ψ.LFunction 1‖ * ‖(χ*ψ).LFunction 1‖ : ℝ):ℂ) := by
      dsimp only [P]
      rw [Complex.ofReal_mul,Complex.ofReal_mul]
      exact congrArg₂ (·*·)
        (congrArg₂ (·*·) (quadratic_LFunction_one_eq_norm hχ hχ₀)
          (quadratic_LFunction_one_eq_norm hψ hψ₀))
        (quadratic_LFunction_one_eq_norm hpq hprod)
    refine H (Q:=q) (P:=P) (a:=estermannFourCoeffs χ ψ) (NeZero.pos q)
      hP ?_ hres (by positivity) (estermannFourCoeffs_nonneg χ ψ hχ hψ)
      (estermannFourCoeffs_apply_one χ ψ)
      (fun _ hs => estermannFourCoeffs_summable χ ψ hs)
      (fun _ hs => (estermannFour_LSeries_eq χ ψ hs).symm) hβ hβ' ?_
    · intro s hs
      calc
        ‖P s‖ = ‖χ.LFunction s‖ * ‖ψ.LFunction s‖ * ‖(χ*ψ).LFunction s‖ := by
          simp only [P,norm_mul]
        _ ≤ (64*(q:ℝ))*(64*(q:ℝ))*(64*(q:ℝ)) :=
          mul_le_mul
            (mul_le_mul (norm_LFunction_estermann_disk χ hχ₀ hs)
              (norm_LFunction_estermann_disk ψ hψ₀ hs) (norm_nonneg _) (by positivity))
            (norm_LFunction_estermann_disk (χ*ψ) hprod hs) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    · simp [P,hzero]

end FareyGoldbach
