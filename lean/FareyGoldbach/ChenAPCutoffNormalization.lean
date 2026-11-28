import FareyGoldbach.ChenCanonicalComparisons

/-! # Singular-product normalization with a variable auxiliary modulus -/

open Filter
open scoped Topology

namespace FareyGoldbach

/-- A possibly varying modulus is allowed at every source size. -/
def ChenAPModuli (r : ℕ→ℕ) : Prop := ∀ N, 2≤N → 0<r N ∧ r N≤N

theorem chenAPCutoff_tendsto (r : ℕ→ℕ) (hr : ChenAPModuli r)
    {a : ℝ} (ha : 0<a) (ha₁ : a≤1) :
    Tendsto (fun N : ℕ => chenDensityProduct (r N*N) (chenPowerLevel a N)*
      Real.log (chenPowerLevel a N:ℝ)/chenCanonicalU (r N*N)) chenEvenAtTop
      (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  let w := chenPowerLevel a
  let R (N : ℕ) := chenCanonicalU (r N*N)/chenSingularAtCutoff (r N*N) (w N)
  have hw := chenPowerLevel_tendsto_atTop ha
  have hw' := (tendsto_natCast_atTop_atTop (R:=ℝ)).comp hw
  have hlog := chenLogTwo_div_powerLevel_tendsto ha
  have hdom : Tendsto (fun N : ℕ => 8*(Real.log (2*(N:ℝ))/(w N:ℝ))+2/(w N:ℝ)) atTop (𝓝 0) := by
    simpa only [w,Function.comp_apply,mul_zero,add_zero] using
      (hlog.const_mul (8:ℝ)).add ((tendsto_const_nhds (x:=(2:ℝ))).div_atTop hw')
  have hexp := (hdom.mono_left (show chenEvenAtTop≤atTop from inf_le_left)).rexp.sub_const 1
  simp only [Real.exp_zero,sub_self] at hexp
  have hR : Tendsto R chenEvenAtTop (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hexp
    apply eventually_inf_principal.mpr
    filter_upwards [hw.eventually_ge_atTop 4,eventually_ge_atTop (2:ℕ)] with N hw₄ hN he
    obtain ⟨hr₁,hrN⟩ := hr N hN
    have hNN : N≤r N*N := Nat.le_mul_of_pos_left _ hr₁
    have he' : Even (r N*N) := Even.mul_left he _
    have hwR : (4:ℝ)≤w N := by exact_mod_cast hw₄
    have hw₀ : (0:ℝ)<w N := by linarith
    have hNr : (2:ℝ)≤N := by exact_mod_cast hN
    have hrr : (r N:ℝ)≤N := by exact_mod_cast hrN
    have hNpos : (0:ℝ)<N := by linarith
    have hrpos : (0:ℝ)<r N := by exact_mod_cast hr₁
    have hℓ : 0≤Real.log (2*(N:ℝ)) := Real.log_nonneg (by linarith)
    have hlog' : Real.log (2*((r N*N:ℕ):ℝ)) ≤ 2*Real.log (2*(N:ℝ)) := by
      rw [Nat.cast_mul]
      calc
        _ ≤ Real.log ((2*(N:ℝ))^2) := Real.log_le_log (by positivity)
          (by nlinarith only [mul_le_mul_of_nonneg_right hrr hNpos.le,sq_nonneg (N:ℝ)])
        _ = _ := by rw [Real.log_pow]; norm_num
    have hi : 1/((w N:ℝ)-1)≤2/(w N:ℝ) :=
      (div_le_div_iff₀ (by linarith) hw₀).mpr (by linarith)
    have h₁ : 2*Real.log (2*((r N*N:ℕ):ℝ))/((w N:ℝ)-1)≤8*(Real.log (2*(N:ℝ))/(w N:ℝ)) := by
      calc _ ≤ (4*Real.log (2*(N:ℝ)))/((w N:ℝ)-1) :=
                div_le_div_of_nonneg_right (by linarith only [hlog']) (by linarith)
           _ = (4*Real.log (2*(N:ℝ)))*(1/((w N:ℝ)-1)) := by ring
           _ ≤ (4*Real.log (2*(N:ℝ)))*(2/(w N:ℝ)) :=
                mul_le_mul_of_nonneg_left hi (by positivity)
           _ = _ := by ring
    have h₂ : 1/((w N:ℝ)-2)≤2/(w N:ℝ) :=
      (div_le_div_iff₀ (by linarith) hw₀).mpr (by linarith)
    change ‖R N-1‖≤Real.exp (_+_)-1
    rw [Real.norm_eq_abs]
    exact (chenCanonicalU_ratio_sub_one_le he' hw₄
      ((chenPowerLevel_le_self ha₁ (by omega)).trans (hNN.trans (Nat.le_succ _)))).trans
      (sub_le_sub_right (Real.exp_le_exp.mpr (add_le_add h₁ h₂)) _)
  have h := ((chenMertensProduct_tendsto.comp hw).mono_left
    (show chenEvenAtTop≤atTop from inf_le_left)).div hR one_ne_zero
  rw [div_one] at h
  apply h.congr'
  apply eventually_inf_principal.mpr
  filter_upwards [hw.eventually_ge_atTop 1] with N hw₁ _
  change Real.log (w N:ℝ)*chenMertensProduct (w N)/R N=_
  rw [chenDensityProduct_eq_mertens_mul_singular hw₁]
  dsimp only [R]
  rw [div_div_eq_mul_div]
  ring

end FareyGoldbach
