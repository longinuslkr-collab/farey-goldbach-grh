import FareyGoldbach.UnconditionalZeroFree
import FareyGoldbach.ChenSwitchingScales

/-! # A uniform zero-free rectangle at logarithmic conductors and heights -/

open Filter
open scoped Topology

namespace FareyGoldbach

private theorem eventually_loglog_le_root (J : ℕ) :
    ∀ᶠ X : ℕ in atTop,
      (J:ℝ)*Real.log (Real.log (X:ℝ)) ≤ 2*Real.sqrt (Real.log (X:ℝ)) := by
  have h := (isLittleO_log_rpow_rpow_atTop (1:ℝ)
    (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have h' : Tendsto (fun L : ℝ => (J:ℝ)*(Real.log L / Real.sqrt L)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,←Real.sqrt_eq_rpow,mul_zero] using h.const_mul (J:ℝ)
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [(h'.comp hL).eventually_lt_const (by norm_num : (0:ℝ)<2),
    hL.eventually_ge_atTop 1] with X hX hX₁
  let L := Real.log (X:ℝ)
  change 1≤L at hX₁
  have hp : 0<Real.sqrt L := Real.sqrt_pos.mpr (by linarith only [hX₁])
  change (J:ℝ)*(Real.log L/Real.sqrt L)<2 at hX
  rw [←mul_div_assoc] at hX
  exact ((div_lt_iff₀ hp).mp hX).le

private theorem smallConductor_log_height_le {L : ℝ} {q A k : ℕ} [NeZero q]
    (hL : 10≤L) (hq : (q:ℝ)≤L^A) {t : ℝ} (ht : |t|≤L^k+2) :
    Real.log (2*(q:ℝ)*(2+|t|))≤((A+k+1:ℕ):ℝ)*Real.log L := by
  have hL₁ : 1≤L := by linarith
  have hT : 1≤L^k := one_le_pow₀ hL₁
  have hq₀ : (0:ℝ)<q := Nat.cast_pos.mpr (NeZero.pos q)
  have ht' : 2+|t|≤5*L^k := by linarith only [ht,hT]
  have hbound : 2*(q:ℝ)*(2+|t|)≤L^(A+k+1) := by
    calc
      _ ≤ (2*L^A)*(5*L^k) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hq (by norm_num)) ht' (by positivity)
          (by positivity)
      _ = 10*(L^A*L^k) := by ring
      _ ≤ L*(L^A*L^k) := mul_le_mul_of_nonneg_right hL (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_one]; ring
  exact (Real.log_le_log (by positivity) hbound).trans_eq (Real.log_pow L _)

private theorem lower_power_conductor {L : ℝ} {q A : ℕ} [NeZero q]
    (hL : 1≤L) (hq : (q:ℝ)≤L^A) :
    (Real.sqrt L)⁻¹ ≤ (q:ℝ)^(-(1/(2*((A:ℝ)+1)))) := by
  let ε : ℝ := 1/(2*((A:ℝ)+1))
  have hA := Nat.cast_nonneg (α:=ℝ) A
  have hε : 0<ε := by dsimp only [ε]; positivity
  have hden : 0<2*((A:ℝ)+1) := by positivity
  have hAu : (A:ℝ)*ε≤1/2 := by
    dsimp only [ε]
    rw [mul_one_div,div_le_iff₀ hden]
    linarith
  have hL₀ := zero_lt_one.trans_le hL
  have hq₀ : (0:ℝ)<q := Nat.cast_pos.mpr (NeZero.pos q)
  calc
    _ = L^(-(1/2:ℝ)) := by rw [Real.sqrt_eq_rpow,Real.rpow_neg hL₀.le]
    _ ≤ L^((A:ℝ)*(-ε)) := Real.rpow_le_rpow_of_exponent_le hL (by linarith only [hAu])
    _ = (L^A)^(-ε) := by rw [Real.rpow_mul hL₀.le,Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos hq₀ hq (neg_nonpos.mpr hε.le)

/-- A rectangle of half-width twice the chosen gap is zero-free, with room
for the local logarithmic-derivative disks around its boundary. -/
theorem eventually_smallConductor_rectangle_geometry (A k : ℕ) :
    ∃ a : ℝ, 0<a ∧ a≤1/16 ∧ ∀ᶠ X : ℕ in atTop,
      let L := Real.log (X:ℝ)
      let T := L^k
      let η := a/Real.sqrt L
      10≤L ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → (q:ℝ)≤L^A →
        (∀ t : ℝ, |t|≤T+2 → Real.log (2*(q:ℝ)*(2+|t|))≤2*Real.sqrt L) ∧
        (∀ z : ℂ, 1-2*η≤z.re → |z.im|≤T+2 → entireL χ z≠0) := by
  let ε : ℝ := 1/(2*((A:ℝ)+1))
  have hε : 0<ε := by dsimp only [ε]; positivity
  obtain ⟨c,hc,hfree⟩ := unconditional_zero_free_region ε hε
  let a := min (c/4) (1/16)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha₁ : a≤1/16 := min_le_right ..
  have hca : 4*a≤c := by
    dsimp only [a]
    linarith only [min_le_left (c/4) (1/16)]
  refine ⟨a,ha,ha₁,?_⟩
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [hL.eventually_ge_atTop 10,eventually_loglog_le_root (A+k+1)] with X hX hroot
  let L := Real.log (X:ℝ)
  let T := L^k
  let η := a/Real.sqrt L
  change 10≤L at hX
  have hL₁ : 1≤L := by linarith
  have hsqrt : 0<Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
  refine ⟨hX,?_⟩
  intro q _ χ hprim hq
  have H (t : ℝ) (ht : |t|≤T+2) : Real.log (2*(q:ℝ)*(2+|t|))≤2*Real.sqrt L :=
    (smallConductor_log_height_le hX hq ht).trans hroot
  refine ⟨H,?_⟩
  intro z hz hzt
  have hm : 2*η≤min (c/Real.log (2*(q:ℝ)*(2+|z.im|))) (c*(q:ℝ)^(-ε)) := by
    apply le_min
    · have hp : 0<Real.log (2*(q:ℝ)*(2+|z.im|)) :=
        zero_lt_one.trans_le (one_le_log_two_mul_d_mul q z.im)
      apply (le_div_iff₀ hp).mpr
      calc
        _ ≤ 2*η*(2*Real.sqrt L) := by
          exact mul_le_mul_of_nonneg_left (H z.im hzt) (by dsimp only [η]; positivity)
        _ = 4*a := by dsimp only [η]; field_simp; ring
        _ ≤ c := hca
    · have hp : (Real.sqrt L)⁻¹≤(q:ℝ)^(-ε) := lower_power_conductor hL₁ hq
      calc
        _ = (2*a)*(Real.sqrt L)⁻¹ := by dsimp only [η]; rw [div_eq_mul_inv]; ring
        _ ≤ c*(Real.sqrt L)⁻¹ := mul_le_mul_of_nonneg_right (by linarith only [hca,ha])
          (inv_nonneg.mpr hsqrt.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left hp hc.le
  exact hfree q χ hprim z ((sub_le_sub_left hm 1).trans hz)

end FareyGoldbach
