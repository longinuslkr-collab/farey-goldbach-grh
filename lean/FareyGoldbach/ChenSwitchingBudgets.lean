import FareyGoldbach.ChenSwitchingScales

/-! # Logarithmic powers in the switching estimates -/

namespace FareyGoldbach

private theorem chen_log_quotient {L n : ℝ} (hL : 1≤L) (hn : 0≤n)
    (a b c : ℕ) (hab : a+c≤b) : L^a*(n/L^b)≤n/L^c := by
  have hpos := zero_lt_one.trans_le hL
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hpos b) (pow_pos hpos c)).mpr
  calc L^a*n*L^c = n*L^(a+c) := by rw [pow_add]; ring
    _ ≤ n*L^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hab) hn

theorem chenSwitchBox_budget_absorb {L n H R C : ℝ}
    (hL : 1≤L) (hn : 0≤n) (hH : 0≤H) (hR : 0<R) (hC : 0≤C)
    (hRlo : L^12≤R) (hRhi : R≤2*L^12) :
    R*(C*(n/L^30+H*L)) + 100000*L^2*(n/R+H+H) ≤
      (2*C+200000)*(n/L^7+H*L^16) := by
  have hl := zero_lt_one.trans_le hL
  have h₁ := chen_log_quotient hL hn 12 30 7 (by norm_num)
  have h₂ := chen_log_quotient hL hn 2 12 7 (by norm_num)
  have h₃ : L^12*(H*L)≤H*L^16 := by
    calc L^12*(H*L) = H*L^13 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 13≤16)) hH
  have h₄ : L^2*H≤H*L^16 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 2≤16)) hH
  have hd₀ : n/R≤n/L^12 := (div_le_div_iff₀ hR (pow_pos hl 12)).mpr
    (mul_le_mul_of_nonneg_left hRlo hn)
  have hd : L^2*(n/R)≤n/L^7 := (mul_le_mul_of_nonneg_left hd₀ (sq_nonneg L)).trans h₂
  have hsmall : R*(C*(n/L^30+H*L))≤2*C*(n/L^7+H*L^16) := calc
    _ ≤ (2*L^12)*(C*(n/L^30+H*L)) := mul_le_mul_of_nonneg_right hRhi (by positivity)
    _ = 2*C*(L^12*(n/L^30)+L^12*(H*L)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₁ h₃) (by positivity)
  have hlarge : 100000*L^2*(n/R+H+H)≤200000*(n/L^7+H*L^16) := by
    have hsum := add_le_add (add_le_add hd h₄) h₄
    have hx := div_nonneg hn (pow_nonneg hl.le 7)
    calc _ = 100000*(L^2*(n/R)+L^2*H+L^2*H) := by ring
      _ ≤ 100000*(n/L^7+H*L^16+H*L^16) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ _ := by linarith only [hx]
  calc _ ≤ 2*C*(n/L^7+H*L^16) + 200000*(n/L^7+H*L^16) := add_le_add hsmall hlarge
    _ = _ := by ring

theorem chenSwitchTotal_budget_absorb {L n H C : ℝ}
    (hL : 1≤L) (hn : 0≤n) (hH : 0≤H) (hC : 0≤C) :
    4*L^3*H + 6*L^3*((2*C+200000)*(n/L^7+H*L^16)) ≤
      (4+6*(2*C+200000))*(n/L^4+H*L^20) := by
  have h₁ := chen_log_quotient hL hn 3 7 4 (by norm_num)
  have h₂ : L^3*(H*L^16) ≤ H*L^20 := by
    calc L^3*(H*L^16) = H*L^19 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 19≤20)) hH
  have h₃ : L^3*H ≤ n/L^4+H*L^20 := by
    calc L^3*H = H*L^3 := mul_comm .. 
      _ ≤ H*L^20 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by norm_num : 3≤20)) hH
      _ ≤ _ := le_add_of_nonneg_left (div_nonneg hn (by positivity))
  calc
    _ = 4*(L^3*H)+(6*(2*C+200000))*(L^3*(n/L^7)+L^3*(H*L^16)) := by ring
    _ ≤ 4*(n/L^4+H*L^20)+(6*(2*C+200000))*(n/L^4+H*L^20) :=
      add_le_add (mul_le_mul_of_nonneg_left h₃ (by norm_num))
        (mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (by positivity))
    _ = _ := by ring

end FareyGoldbach
