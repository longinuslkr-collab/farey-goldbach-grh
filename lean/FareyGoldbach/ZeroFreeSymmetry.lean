import FareyGoldbach.LocalLogDerivative

/-! # Conjugate symmetry of the entire function for quadratic characters -/

open Complex Filter Set
open scoped ComplexConjugate Topology Classical

namespace FareyGoldbach

theorem quadratic_char_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ^2=1) (n : ZMod d) : conj (χ n) = χ n := by
  by_cases hn : IsUnit n
  · have h : χ n ^ 2 = 1 := by
      have h := congrArg (fun ψ : DirichletCharacter ℂ d => ψ n) hχ
      simpa only [sq,MulChar.mul_apply,MulChar.one_apply hn] using h
    rcases sq_eq_one_iff.mp h with h | h <;> simp [h]
  · simp [MulChar.map_nonunit _ hn]

private theorem quadratic_Lseries_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ^2=1) (s : ℂ) :
    conj (LSeries (fun n : ℕ => χ (n:ZMod d)) (conj s)) = LSeries (fun n : ℕ => χ (n:ZMod d)) s := by
  rw [LSeries,Complex.conj_tsum,LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn]
  · simp only [LSeries.term_of_ne_zero hn,map_div₀,quadratic_char_conj hχ]
    rw [← Complex.conj_cpow _ _ (by simp [Complex.natCast_arg, Real.pi_ne_zero.symm])]
    simp

theorem quadratic_entireL_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ^2=1) (s : ℂ) : entireL χ (conj s) = conj (entireL χ s) := by
  let F := entireL χ
  let G : ℂ→ℂ := fun z => conj (F (conj z))
  have hdiff : Differentiable ℂ G := by
    intro z
    change DifferentiableAt ℂ (conj ∘ F ∘ conj) z
    simpa only [Complex.conj_conj] using (differentiable_entireL χ (conj z)).conj_conj
  have he : G = F := by
    apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hdiff).eq_of_eventuallyEq (analyticOnNhd_entireL χ) (z₀:=(2:ℂ))
    have hN : ∀ᶠ z : ℂ in 𝓝 (2:ℂ), 1<z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hN] with z hz
    have h₁ : z≠1 := fun he => by simp [he] at hz
    have h₂ : conj z ≠ 1 := fun he => by
      have := congrArg Complex.re he
      simp at this
      linarith
    have hc : 1<(conj z).re := by simpa using hz
    have hls := quadratic_Lseries_conj hχ z
    change conj (entireL χ (conj z)) = entireL χ z
    rw [entireL_apply_of_ne_one χ h₂,entireL_apply_of_ne_one χ h₁,
      χ.LFunction_eq_LSeries hc,χ.LFunction_eq_LSeries hz]
    by_cases h : χ=1 <;> simp only [h,ite_true,ite_false,map_mul,map_sub,Complex.conj_conj,map_one] at hls ⊢ <;>
      rw [hls]
  have hv := congrFun he (conj s)
  simpa [G,F] using hv.symm

theorem quadratic_LFunction_conj {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    (hχ : χ^2=1) (h₁ : χ≠1) (s : ℂ) : χ.LFunction (conj s) = conj (χ.LFunction s) := by
  simpa only [entireL,ite_eq_right h₁] using quadratic_entireL_conj hχ s

end FareyGoldbach
