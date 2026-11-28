import FareyGoldbach.EstermannTaylorMathlib
import FareyGoldbach.PrimeSums

/-! # Taylor coefficients of a pole-subtracted Dirichlet series -/

open Filter
open scoped Topology

namespace FareyGoldbach

noncomputable def estermannCoeff (F : ℂ→ℂ) (n : ℕ) : ℂ :=
  (-1:ℂ)^n * iteratedDeriv n F 2 / (n.factorial:ℂ)

@[simp] theorem estermannCoeff_zero (F : ℂ→ℂ) : estermannCoeff F 0=F 2 := by
  simp [estermannCoeff]

private theorem estermann_pole_coeff (res : ℝ) (n : ℕ) :
    estermannCoeff (fun s : ℂ => (res:ℂ)/(s-1)) n=(res:ℂ) := by
  have hu := (iteratedDerivWithin_one_div (𝕜:=ℂ) n isOpen_univ) (Set.mem_univ (1:ℂ))
  simp only [iteratedDerivWithin_univ,one_zpow,mul_one] at hu
  have hp : iteratedDeriv n (fun z : ℂ => (res:ℂ)/(z-1)) 2 =
      (res:ℂ)*((-1:ℂ)^n*(n.factorial:ℂ)) := by
    simp_rw [show (fun s : ℂ => (res:ℂ)/(s-1)) =
      (fun s : ℂ => (res:ℂ)*((fun v : ℂ => 1/v) (s-1))) by funext s; ring]
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_comp_sub_const n (fun v : ℂ => 1/v) 1]
    norm_num only [show (2:ℂ)-1=1 by norm_num]
    rw [hu]
  have h1 : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [←mul_pow]; simp
  unfold estermannCoeff
  rw [hp]
  have hfac : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [show (-1:ℂ)^n*((res:ℂ)*((-1)^n*(n.factorial:ℂ))) =
    ((-1:ℂ)^n*(-1)^n)*(res:ℂ)*(n.factorial:ℂ) by ring,h1,one_mul,
    mul_div_cancel_right₀ _ hfac]

theorem estermann_coeff_add_pole {F G : ℂ→ℂ} {res : ℝ}
    (hG : DiffContOnCl ℂ G (Metric.ball 2 (3/2:ℝ)))
    (hnear : F =ᶠ[𝓝 (2:ℂ)] (fun s => G s+(res:ℂ)/(s-1))) (n : ℕ) :
    estermannCoeff F n=estermannCoeff G n+(res:ℂ) := by
  have hGc : ContDiffAt ℂ n G (2:ℂ) :=
    (hG.differentiableOn.analyticAt (Metric.ball_mem_nhds _ (by norm_num))).contDiffAt
  have hp : ContDiffAt ℂ n (fun s : ℂ => (res:ℂ)/(s-1)) 2 := by fun_prop (disch := norm_num)
  rw [←estermann_pole_coeff res n]
  simp only [estermannCoeff,(hnear.iteratedDeriv_eq n),iteratedDeriv_fun_add hGc hp]
  ring

theorem estermann_coeff_norm_bound {G : ℂ→ℂ} {B : ℝ}
    (hG : DiffContOnCl ℂ G (Metric.ball 2 (3/2:ℝ)))
    (hB : ∀ s∈Metric.sphere (2:ℂ) (3/2:ℝ), ‖G s‖≤B) (n : ℕ) :
    ‖estermannCoeff G n‖≤B/(3/2:ℝ)^n := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (by norm_num) hG hB
  simp only [estermannCoeff,norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))).mpr
  exact h.trans_eq (by ring)

theorem estermann_hasSum_real {G : ℂ→ℂ} {β : ℝ} (hβ : 7/8≤β) (hβ' : β<1)
    (hG : DiffContOnCl ℂ G (Metric.ball 2 (3/2:ℝ))) :
    HasSum (fun n : ℕ => (2-β)^n*(estermannCoeff G n).re) (G β).re := by
  have hz : (β:ℂ)∈Metric.ball 2 (3/2:ℝ) := by
    rw [Metric.mem_ball,dist_eq_norm,←Complex.ofReal_ofNat,←Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonpos (by linarith : β-2≤0)]
    linarith
  have h := Complex.hasSum_taylorSeries_on_ball hG.differentiableOn hz
  apply (Complex.hasSum_re h).congr_fun
  intro n
  have he : ((β:ℂ)-2)^n = (((2-β:ℝ):ℂ)^n)*(-1:ℂ)^n := by
    rw [←mul_pow,Complex.ofReal_sub]
    norm_num
  simp only [smul_eq_mul,he,estermannCoeff,div_eq_mul_inv]
  rw [show (n.factorial:ℂ)⁻¹*(((2-β:ℝ):ℂ)^n*(-1)^n*iteratedDeriv n G 2) =
    ((2-β:ℝ):ℂ)^n*((-1)^n*iteratedDeriv n G 2*(n.factorial:ℂ)⁻¹) by ring,
    ← Complex.ofReal_pow,Complex.re_ofReal_mul]

open scoped ComplexOrder in
theorem estermann_lseries_coeff_nonneg {a : ℕ→ℂ} (ha : ∀ n,0≤a n) (ha1 : a 1=1)
    (hs : ∀ s : ℂ,1<s.re → LSeriesSummable a s) {F : ℂ→ℂ}
    (he : F =ᶠ[𝓝 (2:ℂ)] LSeries a) :
    1≤(F 2).re ∧ ∀ n, 0≤(estermannCoeff F n).re := by
  have hab := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x:=1)
    (fun y hy => hs y (by simpa using hy))
  have hm : LSeries.abscissaOfAbsConv a < (2:ℝ) := hab.trans_lt (EReal.coe_lt_coe_iff.mpr (by norm_num))
  constructor
  · have hss := hs 2 (by norm_num)
    have hone := hss.le_tsum 1 (fun n _ => LSeries.term_nonneg (ha n) 2)
    rw [LSeries.term_of_ne_zero one_ne_zero, Nat.cast_one,Complex.one_cpow,div_one,ha1] at hone
    rw [he.eq_of_nhds]
    exact (Complex.le_def.mp hone).1
  · intro n
    have h := LSeries.iteratedDeriv_alternating ha hm n
    have h' := (Complex.le_def.mp h).1
    simp only [estermannCoeff,he.iteratedDeriv_eq n,←Complex.ofReal_natCast,
      Complex.div_ofReal_re]
    exact div_nonneg h' (Nat.cast_nonneg _)

end FareyGoldbach
