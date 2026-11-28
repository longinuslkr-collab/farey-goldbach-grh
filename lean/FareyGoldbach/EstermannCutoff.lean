import FareyGoldbach.PrimeSums

/-! # Truncating an analytic expansion with a conductor-dependent bound -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- The geometric tail is uniformly small after a logarithmic cutoff, while
the evaluation immediately to the left of one costs only a small power. -/
theorem estermann_log_cutoff (A : ℝ) (hA : 0<A) :
    ∃ C : ℝ, 0<C ∧ ∀ {Q : ℕ}, 1≤Q → ∃ K : ℕ, 1≤K ∧
      4*(A*(Q:ℝ)^10)*(3/4:ℝ)^K ≤ 1/2 ∧
      ∀ δ : ℝ, 0≤δ → (1+δ)^K ≤ (2*(Q:ℝ))^(C*δ) := by
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤3/4)
    (by norm_num : (3/4:ℝ)<1)).const_mul (4*A)
  rw [mul_zero] at ht
  obtain ⟨k,hk,hk'⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (ht.eventually_lt_const (by norm_num : (0:ℝ)<1/2))).exists
  refine ⟨2*(k:ℝ)+80,by positivity,?_⟩
  intro Q hQ
  let j := Nat.log 2 Q+1
  let K := k+40*j
  have hqr : (1:ℝ)≤Q := Nat.one_le_cast.mpr hQ
  have hp : (0:ℝ)<Q := zero_lt_one.trans_le hqr
  have hj : (Q:ℝ)≤(2:ℝ)^j := by exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1<2) Q).le
  have hpow : (Q:ℝ)^10 ≤ ((2:ℝ)^10)^j := by
    rw [←pow_mul, mul_comm 10, pow_mul]
    exact pow_le_pow_left₀ hp.le hj 10
  have hcut : (Q:ℝ)^10*(3/4:ℝ)^(40*j) ≤ 1 := by
    rw [pow_mul]
    calc _ ≤ ((2:ℝ)^10)^j*((3/4:ℝ)^40)^j := mul_le_mul_of_nonneg_right hpow (by positivity)
         _ = ((2:ℝ)^10*(3/4:ℝ)^40)^j := (mul_pow ..).symm
         _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hlog : (j:ℝ)≤2*Real.log (2*(Q:ℝ)) := by
    have hh : (2:ℝ)^(Nat.log 2 Q)≤(Q:ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega : Q≠0)
    have h := Real.log_le_log (by positivity) hh
    rw [Real.log_pow] at h
    rw [Real.log_mul (by norm_num) hp.ne']
    dsimp [j]
    push_cast
    have h₂ := Real.log_two_gt_d9
    have hb : 1/2≤Real.log 2 := by linarith only [h₂]
    nlinarith only [h,hb,mul_nonneg (Nat.cast_nonneg (α:=ℝ) (Nat.log 2 Q)) (sub_nonneg.mpr hb)]
  have hlog₁ : 1/2≤Real.log (2*(Q:ℝ)) :=
    (show 1/2≤Real.log 2 by linarith only [Real.log_two_gt_d9]).trans
      (Real.log_le_log (by norm_num) (by linarith))
  have hK : (K:ℝ)≤(2*(k:ℝ)+80)*Real.log (2*(Q:ℝ)) := by
    dsimp only [K]; push_cast
    nlinarith only [hlog,mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (sub_nonneg.mpr hlog₁)]
  refine ⟨K,by dsimp [K]; omega,?_,?_⟩
  · change 4*(A*(Q:ℝ)^10)*(3/4:ℝ)^(k+40*j) ≤ _
    rw [pow_add]
    calc _ = (4*A*(3/4:ℝ)^k)*((Q:ℝ)^10*(3/4:ℝ)^(40*j)) := by ring
         _ ≤ (4*A*(3/4:ℝ)^k)*1 := mul_le_mul_of_nonneg_left hcut (by positivity)
         _ ≤ _ := by simpa only [mul_one] using hk'.le
  · intro δ hδ
    have h : 1+δ≤Real.exp δ := by linarith only [Real.add_one_le_exp δ]
    calc _ ≤ (Real.exp δ)^K := pow_le_pow_left₀ (by positivity) h K
         _ = Real.exp ((K:ℝ)*δ) := (Real.exp_nat_mul δ K).symm
         _ ≤ Real.exp (Real.log (2*(Q:ℝ))*((2*(k:ℝ)+80)*δ)) :=
           Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hK hδ).trans_eq (by ring))
         _ = _ := (Real.rpow_def_of_pos (by positivity) _).symm

end FareyGoldbach
