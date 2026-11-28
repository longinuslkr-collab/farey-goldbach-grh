import FareyGoldbach.SharpPerronKernel

/-! # Explicit estimates for the powers in the small-conductor Perron shift -/

namespace FareyGoldbach

theorem smallConductor_rpow_right {x : ℝ} (hx : 0<x) (hL : 1≤Real.log x) :
    x^(1+(Real.log x)⁻¹)≤3*x := by
  have hl := zero_lt_one.trans_le hL
  have he : Real.log x*(1+(Real.log x)⁻¹)=Real.log x+1 := by
    rw [mul_add,mul_one,mul_inv_cancel₀ hl.ne']
  rw [Real.rpow_def_of_pos hx,he,Real.exp_add,Real.exp_log hx,mul_comm]
  have hb := Real.abs_exp_sub_one_le (x:=1) (by norm_num)
  norm_num at hb
  exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self (Real.exp 1-1)]) hx.le

/-- Taking one explicit term in the exponential series covers the vertical edge. -/
theorem smallConductor_left_power {x a : ℝ} (B : ℕ) (hx : 0<x)
    (hL : 1≤Real.log x) (ha : 0<a) :
    let L := Real.log x
    x^(1-a/Real.sqrt L)*L*L^(2*B+12) ≤
      ((2*(3*B+13)).factorial:ℝ)/a^(2*(3*B+13))*(x/L^B) := by
  let L := Real.log x
  let n := 3*B+13
  have hl : 0<L := zero_lt_one.trans_le hL
  have hs := Real.sqrt_pos.mpr hl
  have hLs : L*(a/Real.sqrt L)=a*Real.sqrt L := by
    calc
      _ = (Real.sqrt L)^2*(a/Real.sqrt L) :=
        congrArg (fun u : ℝ => u*(a/Real.sqrt L)) (Real.sq_sqrt hl.le).symm
      _ = _ := by field_simp
  have hpow : x^(1-a/Real.sqrt L)=x/Real.exp (a*Real.sqrt L) := by
    rw [Real.rpow_def_of_pos hx,mul_sub,mul_one,hLs,Real.exp_sub,Real.exp_log hx]
  have hind : (Real.sqrt L)^(2*n)=L^n := by rw [pow_mul,Real.sq_sqrt hl.le]
  have hfac : 0<((2*n).factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hexp := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (a*Real.sqrt L)
    (mul_nonneg ha.le hs.le) (2*n))
  rw [mul_pow,hind] at hexp
  have he : L^n/Real.exp (a*Real.sqrt L)≤((2*n).factorial:ℝ)/a^(2*n) := by
    rw [div_le_div_iff₀ (Real.exp_pos _) (pow_pos ha _)]
    linarith only [hexp]
  have hprod : L*L^(2*B+12)*L^B=L^n := by
    calc
      _ = L^(1+(2*B+12)+B) := by simp only [pow_add,pow_one]
      _ = _ := by dsimp [n]; congr 1; omega
  change x^(1-a/Real.sqrt L)*L*L^(2*B+12) ≤ ((2*n).factorial:ℝ)/a^(2*n)*(x/L^B)
  calc
    _ = L^n/Real.exp (a*Real.sqrt L)*(x/L^B) := by
      rw [hpow,←hprod]
      field_simp [hl.ne',Real.exp_ne_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_right he (by positivity)

theorem smallConductor_power_budget {x a : ℝ} (B : ℕ) (hx : 0<x)
    (hL : 1≤Real.log x) (ha : 0<a) :
    let L := Real.log x
    let δ := (L^(B+3))⁻¹
    let T := L^(2*B+12)
    let σ := 1+L⁻¹
    let η := a/Real.sqrt L
    (x^(1-η)*L*T ≤ ((2*(3*B+13)).factorial:ℝ)/a^(2*(3*B+13))*(x/L^B)) ∧
    (x^σ*L/(δ^2*T^2)≤3*(x/L^B)) ∧ (δ*x*L≤x/L^B) ∧
    (x^σ*L/(δ^2*T^3)≤3*(x/L^B)) := by
  let L := Real.log x
  let δ := (L^(B+3))⁻¹
  let T := L^(2*B+12)
  let σ := 1+L⁻¹
  have hl : 0<L := zero_lt_one.trans_le hL
  have hT : 1≤T := one_le_pow₀ hL
  have hTp := zero_lt_one.trans_le hT
  have hd : 0<δ := by dsimp [δ]; positivity
  have hσ : x^σ≤3*x := smallConductor_rpow_right hx hL
  have hp : L*(L^(B+3))^2*L^B≤T^2 := by
    calc
      _ = L^(1+(B+3)*2+B) := by simp only [pow_add,pow_mul,pow_one]
      _ ≤ L^((2*B+12)*2) := pow_le_pow_right₀ hL (by omega)
      _ = _ := pow_mul ..
  have hratio : L*(L^(B+3))^2/T^2 ≤ 1/L^B := by
    rw [div_le_div_iff₀ (pow_pos hTp _) (pow_pos hl _),one_mul]
    exact hp
  have hh : x^σ*L/(δ^2*T^2)≤3*(x/L^B) := by
    calc
      _ ≤ (3*x)*L/(δ^2*T^2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hσ hl.le) (by positivity)
      _ = (3*x)*(L*(L^(B+3))^2/T^2) := by
        dsimp [δ]; rw [inv_pow,div_mul_eq_div_div,div_inv_eq_mul]; ring
      _ ≤ (3*x)*(1/L^B) := mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by ring
  have hp₁ : L*L^B≤L^(B+3) := by
    calc _ = L^(1+B) := by rw [pow_add,pow_one]
         _ ≤ _ := pow_le_pow_right₀ hL (by omega)
  have hδratio : L/L^(B+3)≤1/L^B := by
    rw [div_le_div_iff₀ (pow_pos hl _) (pow_pos hl _),one_mul]
    exact hp₁
  refine ⟨smallConductor_left_power B hx hL ha,hh,?_,?_⟩
  · calc δ*x*L = x*(L/L^(B+3)) := by dsimp [δ]; ring
         _ ≤ x*(1/L^B) := mul_le_mul_of_nonneg_left hδratio hx.le
         _ = _ := by ring
  · apply le_trans _ hh
    exact div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_pos_of_pos hx σ).le hl.le)
      (mul_pos (pow_pos hd _) (pow_pos hTp _))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by norm_num : 2≤3)) (sq_nonneg δ))

end FareyGoldbach
