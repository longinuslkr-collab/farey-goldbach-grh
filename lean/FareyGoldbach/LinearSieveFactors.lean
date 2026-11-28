module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # First explicit branches of the dimension-one linear-sieve functions -/

public section

namespace FareyGoldbach

/-- The explicit branch of the upper linear-sieve function on `1 ≤ s ≤ 3`. -/
noncomputable def linearSieveUpperFactor (s : ℝ) : ℝ :=
  2*Real.exp Real.eulerMascheroniConstant/s

/-- The explicit branch of the lower linear-sieve function on `2 ≤ s ≤ 4`. -/
noncomputable def linearSieveLowerFactor (s : ℝ) : ℝ :=
  2*Real.exp Real.eulerMascheroniConstant*Real.log (s-1)/s

theorem linearSieveUpperFactor_pos {s : ℝ} (hs : 0<s) : 0<linearSieveUpperFactor s :=
  div_pos (mul_pos (by norm_num) (Real.exp_pos _)) hs

theorem linearSieveLowerFactor_pos {s : ℝ} (hs : 2<s) : 0<linearSieveLowerFactor s :=
  div_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (Real.log_pos (by linarith))) (by linarith)

end FareyGoldbach
