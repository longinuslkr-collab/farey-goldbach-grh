import FareyGoldbach.PrimeSums

/-! # The two-parameter Vaughan convolution identity -/

open ArithmeticFunction
open scoped Classical

namespace FareyGoldbach

noncomputable def vaughanCut (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n≤U then f n else 0, by simp⟩

noncomputable def vaughanTail (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f - vaughanCut U f

theorem vaughanCut_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    vaughanCut U f n = if n≤U then f n else 0 := rfl

theorem vaughanTail_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    vaughanTail U f n = if U<n then f n else 0 := by
  change f n - (if n≤U then f n else 0) = _
  split_ifs <;> first | omega | simp_all

noncomputable def vaughanMu (V : ℕ) : ArithmeticFunction ℝ :=
  vaughanCut V (moebius : ArithmeticFunction ℝ)

noncomputable def vaughanAlpha (U V : ℕ) : ArithmeticFunction ℝ :=
  vaughanMu V * vaughanCut U vonMangoldt

noncomputable def vaughanMuDiv (V : ℕ) : ArithmeticFunction ℝ :=
  vaughanMu V * (zeta : ArithmeticFunction ℝ)

theorem vaughanAlpha_eq_zero_of_lt {U V n : ℕ} (h : U*V<n) : vaughanAlpha U V n = 0 := by
  rw [vaughanAlpha, ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  have hh := (Nat.mem_divisorsAntidiagonal.mp hx).1
  by_cases hx₁ : x.1≤V
  · have hx₂ : ¬ x.2≤U := fun hc => by
      have H := Nat.mul_le_mul hx₁ hc
      rw [hh,Nat.mul_comm V U] at H
      omega
    simp [vaughanCut_apply,hx₂]
  · simp [vaughanMu,vaughanCut_apply,hx₁]

private theorem cut_mu_div (V : ℕ) (hV : 1≤V) : vaughanCut V (vaughanMuDiv V) = 1 := by
  ext n
  rw [vaughanCut_apply]
  by_cases hn : n≤V
  · rw [ite_eq_left hn]
    have he : vaughanMuDiv V n = ((moebius : ArithmeticFunction ℝ)*(zeta : ArithmeticFunction ℝ)) n := by
      simp only [vaughanMuDiv, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro x hx
      have hd := Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
      simp [vaughanMu,vaughanCut_apply,hd.trans hn]
    rw [he, ArithmeticFunction.coe_moebius_mul_coe_zeta]
  · rw [ite_eq_right hn, ArithmeticFunction.one_apply_ne (by omega : n≠1)]

/-- Vaughan's identity. The long divisor variable in the final convolution is
strictly greater than V and the von Mangoldt variable is strictly greater than U. -/
theorem vaughan_identity (U V : ℕ) (hV : 1≤V) :
    vonMangoldt = vaughanCut U vonMangoldt - vaughanAlpha U V*(zeta : ArithmeticFunction ℝ) +
      vaughanMu V*ArithmeticFunction.log - vaughanTail V (vaughanMuDiv V)*vaughanTail U vonMangoldt := by
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  simp only [vaughanTail, cut_mu_div V hV]
  simp only [vaughanAlpha, vaughanMuDiv]
  ring

end FareyGoldbach
