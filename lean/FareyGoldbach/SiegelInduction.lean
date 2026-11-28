import FareyGoldbach.SiegelLocal
import FareyGoldbach.SharpRankin

/-! # Changing levels in the auxiliary real-character product -/

open Finset

namespace FareyGoldbach

/-- The Euler factors removed when inducing a character cost at most Q/φ(Q). -/
theorem norm_LFunction_one_changeLevel_le {q Q : ℕ} [NeZero q] [NeZero Q]
    (h : q∣Q) (χ : DirichletCharacter ℂ q) (hχ : χ≠1) :
    ‖(χ.changeLevel h).LFunction 1‖ ≤ 2*Real.log (2*(Q:ℝ))*‖χ.LFunction 1‖ := by
  classical
  have hprod :
      ‖∏ p∈Q.primeFactors, ((1:ℂ)-χ p*(p:ℂ)^(-(1:ℂ)))‖ ≤ (Q:ℝ)/(Q.totient:ℝ) := by
    rw [norm_prod,div_totient_eq_prod_primeFactors (NeZero.pos Q)]
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) (fun p hp => ?_)
    have hp₂ : (2:ℝ)≤p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
    have hp₀ : (0:ℝ)<p := by linarith only [hp₂]
    have h₁ : ‖χ p*(p:ℂ)^(-(1:ℂ))‖ ≤ (p:ℝ)⁻¹ := by
      rw [norm_mul,Complex.cpow_neg_one,norm_inv,Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)
    calc ‖(1:ℂ)-χ p*(p:ℂ)^(-(1:ℂ))‖ ≤ ‖(1:ℂ)‖+‖χ p*(p:ℂ)^(-(1:ℂ))‖ := norm_sub_le .. 
      _ ≤ 1+(p:ℝ)⁻¹ := by rw [norm_one]; exact add_le_add_right h₁ _
      _ ≤ (p:ℝ)/((p:ℝ)-1) := by
        apply (le_div_iff₀ (by linarith only [hp₂] : 0<(p:ℝ)-1)).mpr
        rw [add_mul,one_mul, mul_sub,inv_mul_cancel₀ hp₀.ne',mul_one]
        linarith only [inv_nonneg.mpr hp₀.le]
  rw [DirichletCharacter.LFunction_changeLevel h χ (Or.inl hχ),norm_mul,mul_comm]
  exact mul_le_mul_of_nonneg_right (hprod.trans (div_totient_le_two_log (NeZero.pos Q))) (norm_nonneg _)

/-- Distinct primitive conductors stay distinct at every common level. For two
quadratic characters this ensures that the product remains nonprincipal. -/
theorem siegel_lifted_pair {q₁ q₂ Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero Q]
    (d₁ : q₁∣Q) (d₂ : q₂∣Q) (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (hp₁ : χ₁.IsPrimitive) (hp₂ : χ₂.IsPrimitive) (hq : 1<q₁) (hlt : q₁<q₂)
    (hquad₁ : χ₁^2=1) (hquad₂ : χ₂^2=1) :
    let ξ₁ := χ₁.changeLevel d₁
    let ξ₂ := χ₂.changeLevel d₂
    ξ₁≠1 ∧ ξ₂≠1 ∧ ξ₁^2=1 ∧ ξ₂^2=1 ∧ ξ₁*ξ₂≠1 ∧ (ξ₁*ξ₂)^2=1 := by
  let ξ₁ := χ₁.changeLevel d₁
  let ξ₂ := χ₂.changeLevel d₂
  have hχ₁ : χ₁≠1 := fun he => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hp₁ he)
  have hχ₂ : χ₂≠1 := fun he => (Nat.ne_of_gt (hq.trans hlt)) (eq_one_of_isPrimitive_of_eq_one hp₂ he)
  have hξ₁ : ξ₁≠1 := fun he => hχ₁ ((DirichletCharacter.changeLevel_eq_one_iff d₁).mp he)
  have hξ₂ : ξ₂≠1 := fun he => hχ₂ ((DirichletCharacter.changeLevel_eq_one_iff d₂).mp he)
  have he₁ : ξ₁^2=1 := by dsimp only [ξ₁]; rw [←map_pow,hquad₁,map_one]
  have he₂ : ξ₂^2=1 := by dsimp only [ξ₂]; rw [←map_pow,hquad₂,map_one]
  refine ⟨hξ₁,hξ₂,he₁,he₂,?_,?_⟩
  · intro h
    change ξ₁*ξ₂=1 at h
    have he : ξ₁=ξ₂ := calc
      ξ₁ = ξ₁*(ξ₂*ξ₂) := by rw [←pow_two,he₂,mul_one]
      _ = ξ₂ := by rw [←mul_assoc,h,one_mul]
    have hc₁ : ξ₁.conductor=q₁ := (χ₁.conductor_changeLevel d₁).trans hp₁
    have hc₂ : ξ₂.conductor=q₂ := (χ₂.conductor_changeLevel d₂).trans hp₂
    exact hlt.ne (hc₁.symm.trans ((congrArg DirichletCharacter.conductor he).trans hc₂))
  · change (ξ₁*ξ₂)^2=1
    rw [mul_pow,he₁,he₂,one_mul]

end FareyGoldbach
