import FareyGoldbach.SiegelLocal

/-! # From a lower bound at one to a real zero-free interval -/

open Set
open scoped Topology

namespace FareyGoldbach

private theorem siegel_log_power_uniform {δ : ℝ} (hδ : 0<δ) :
    ∃ M : ℝ, 0<M ∧ ∀ q : ℕ, 1<q →
      Real.log (2*(q:ℝ))^2 * (q:ℝ)^(-δ)≤M := by
  let M := 2*(2:ℝ)^δ/δ^2
  refine ⟨M,by dsimp only [M]; positivity,?_⟩
  intro q hq
  have hqR : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.le
  have hp := zero_lt_one.trans_le hqR
  let L := Real.log (2*(q:ℝ))
  have hl : 0≤L := Real.log_nonneg (by linarith only [hqR])
  have h := Real.pow_div_factorial_le_exp (δ*L) (mul_nonneg hδ.le hl) 2
  have he : Real.exp (δ*L)=(2:ℝ)^δ*(q:ℝ)^δ := by
    rw [mul_comm,←Real.rpow_def_of_pos (by positivity : 0<2*(q:ℝ)),Real.mul_rpow (by norm_num) hp.le]
  rw [he] at h
  norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    Nat.reduceAdd,mul_one] at h
  change L^2*(q:ℝ)^(-δ)≤M
  rw [Real.rpow_neg hp.le,←div_eq_mul_inv]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hp _)).mpr
  dsimp only [M]
  calc L^2 ≤ 2*((2:ℝ)^δ*(q:ℝ)^δ)/δ^2 :=
        (le_div_iff₀ (sq_pos_of_pos hδ)).mpr (by nlinarith only [h])
    _ = (2*(2:ℝ)^δ/δ^2)*(q:ℝ)^δ := by ring

theorem siegel_real_zero_gap_of_L_one_lower
    (hLower : ∀ ε : ℝ, 0<ε → ∃ c : ℝ, 0<c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → 1<q → χ^2=1 → c*(q:ℝ)^(-ε)≤‖χ.LFunction 1‖)
    (ε : ℝ) (hε : 0<ε) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 1<q → χ^2=1 → ∀ β : ℝ,
        1-c*(q:ℝ)^(-ε)≤β → β<1 → χ.LFunction (β:ℂ)≠0 := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨c₀,hc₀,h₀⟩ := hLower δ hδ
  obtain ⟨M,hM,hbound⟩ := siegel_log_power_uniform hδ
  let c := min (1/(8*M)) (c₀/(256*M))
  have hc : 0<c := lt_min (by positivity) (by positivity)
  have hc₁ : c*(8*M)≤1 := (le_div_iff₀ (by positivity : 0<8*M)).mp (min_le_left ..)
  have hc₂ : c*(256*M)≤c₀ := (le_div_iff₀ (by positivity : 0<256*M)).mp (min_le_right ..)
  refine ⟨c,hc,?_⟩
  intro q _ χ hprim hq hquad β hβ hβ' hzero
  let L := Real.log (2*(q:ℝ))
  let P := (q:ℝ)^(-δ)
  have hqR : (1:ℝ)≤q := Nat.one_le_cast.mpr hq.le
  have hp := zero_lt_one.trans_le hqR
  have hL : 1≤L := (Real.le_log_iff_exp_le (by positivity : 0<2*(q:ℝ))).mpr
    (Real.exp_one_lt_three.le.trans (by have : (2:ℝ)≤q := Nat.cast_le.mpr hq; linarith))
  have hLp := zero_lt_one.trans_le hL
  have hP : 0<P := Real.rpow_pos_of_pos hp _
  have hP' : P≤1 := Real.rpow_le_one_of_one_le_of_nonpos hqR (by linarith only [hδ])
  have heq : (q:ℝ)^(-ε)=P^2 := by
    dsimp only [P]
    rw [pow_two,←Real.rpow_add hp,show -δ + -δ = -ε by dsimp only [δ]; ring]
  rw [heq] at hβ
  have hM' : L^2*P≤M := hbound q hq
  have hLP : L*P^2≤M := by
    apply le_trans _ hM'
    exact mul_le_mul (by nlinarith only [mul_nonneg hLp.le (sub_nonneg.mpr hL)])
      (by nlinarith only [mul_nonneg hP.le (sub_nonneg.mpr hP')]) (sq_nonneg P) (sq_nonneg L)
  have hnear : 1-1/(8*L)≤β := by
    have hstep : c*P^2≤1/(8*L) := by
      apply (le_div_iff₀ (by positivity : 0<8*L)).mpr
      calc c*P^2*(8*L) = (8*c)*(L*P^2) := by ring
        _ ≤ 8*c*M := mul_le_mul_of_nonneg_left hLP (by positivity)
        _ ≤ 1 := by linarith only [hc₁]
    linarith only [hstep,hβ]
  have hχ : χ≠1 := fun hh => (Nat.ne_of_gt hq) (eq_one_of_isPrimitive_of_eq_one hprim hh)
  let F (x : ℝ) := χ.LFunction (x:ℂ)
  have hder (x : ℝ) : HasDerivAt F (deriv χ.LFunction (x:ℂ)) x :=
    ((χ.differentiable_LFunction hχ _).hasDerivAt).comp_ofReal
  have hmv := (convex_Icc β 1).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => (hder x).differentiableAt)
    (C:=128*L^2) (fun x hx => by rw [(hder x).deriv]; exact siegel_deriv_L_real_le χ hprim hq (hnear.trans hx.1) hx.2)
    (left_mem_Icc.mpr hβ'.le) (right_mem_Icc.mpr hβ'.le)
  simp only [F,Complex.ofReal_one,hzero,sub_zero,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hβ'.le)] at hmv
  have hlarge := h₀ q χ hprim hq hquad
  have hup : 128*L^2*(1-β)≤(c₀/2)*P := by
    calc _ ≤ 128*L^2*(c*P^2) := mul_le_mul_of_nonneg_left (by linarith only [hβ]) (by positivity)
      _ = (128*c)*(L^2*P)*P := by ring
      _ ≤ (128*c)*M*P := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hM' (by positivity)) hP.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hc₂]) hP.le
  have hbad : c₀*P≤(c₀/2)*P := hlarge.trans (hmv.trans hup)
  nlinarith only [hbad,mul_pos hc₀ hP]

end FareyGoldbach
