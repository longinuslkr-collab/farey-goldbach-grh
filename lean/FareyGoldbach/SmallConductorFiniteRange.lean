import FareyGoldbach.PrimeSums

/-! # Bounded cutoffs in a uniform Mangoldt estimate -/

open Finset Filter
open scoped Classical

namespace FareyGoldbach

theorem norm_mangoldt_prefix_le_log {q : ℕ} (χ : DirichletCharacter ℂ q)
    {j N : ℕ} (hj : j≤N) :
    ‖∑ n∈Icc 1 j,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n‖≤(j:ℝ)*Real.log N := by
  calc _ ≤ ∑ n∈Icc 1 j,‖(ArithmeticFunction.vonMangoldt n:ℂ)*χ n‖ := norm_sum_le .. 
    _ ≤ ∑ _n∈Icc 1 j,Real.log N := by
      apply sum_le_sum
      intro n hn
      have hnp : 0<(n:ℝ) := Nat.cast_pos.mpr (mem_Icc.mp hn).1
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
        (ArithmeticFunction.vonMangoldt_le_log.trans
          (Real.log_le_log hnp (Nat.cast_le.mpr ((mem_Icc.mp hn).2.trans hj))))
    _ = _ := by simp

theorem smallConductorMangoldt_of_eventual {A B : ℕ} {C : ℝ} (hC : 0<C)
    (hb : ∀ᶠ X : ℕ in atTop, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
        ‖(∑ n∈Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q))-
          (if χ=1 then (X:ℂ) else 0)‖≤C*(X:ℝ)/(Real.log (X:ℝ))^B) :
    ∃ K : ℝ, 0<K ∧ ∀ (X q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 2≤X → (q:ℝ)≤(Real.log (X:ℝ))^A →
        ‖(∑ n∈Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ (n:ZMod q))-
          (if χ=1 then (X:ℂ) else 0)‖≤K*(X:ℝ)/(Real.log (X:ℝ))^B := by
  obtain ⟨N,hN⟩ := eventually_atTop.1 hb
  let H := (N:ℝ)+1
  have hH : 0<H := by dsimp [H]; positivity
  refine ⟨max C (H*H^B),hC.trans_le (le_max_left ..),?_⟩
  intro X q _ χ hχ hX hq
  have hp : 0<(X:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0<Real.log (X:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hX)
  by_cases hx : N≤X
  · exact (hN X hx q χ hχ hX hq).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left ..) hp.le) (pow_nonneg hl.le _))
  · have hXN : (X:ℝ)≤N := Nat.cast_le.mpr (le_of_lt (lt_of_not_ge hx))
    have hsum := norm_mangoldt_prefix_le_log (N:=X) χ le_rfl
    have hcenter : ‖if χ=1 then (X:ℂ) else 0‖≤(X:ℝ) := by split_ifs <;> simp
    have htw := (norm_sub_le (∑ n∈Icc 1 X,(ArithmeticFunction.vonMangoldt n:ℂ)*χ n)
      (if χ=1 then (X:ℂ) else 0)).trans (add_le_add hsum hcenter)
    have hlog := Real.log_le_sub_one_of_pos hp
    have hmass : (Real.log (X:ℝ)+1)≤H := by dsimp only [H]; linarith only [hlog,hXN]
    have hprod := mul_le_mul hmass
      (pow_le_pow_left₀ hl.le (le_trans (by linarith : Real.log (X:ℝ)≤Real.log X+1) hmass) B)
      (pow_nonneg hl.le _) hH.le
    apply (le_div_iff₀ (pow_pos hl _)).mpr
    apply (mul_le_mul_of_nonneg_right htw (pow_nonneg hl.le B)).trans
    calc _ = ((Real.log X+1)*Real.log X^B)*(X:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hprod.trans (le_max_right ..)) hp.le

end FareyGoldbach
