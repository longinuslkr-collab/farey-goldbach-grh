import FareyGoldbach.ChenConditional

/-! # Uniform scales for the progression-restricted Chen sieve -/

open Filter
open scoped Topology

namespace FareyGoldbach

noncomputable def chenAPMassScale (N r : ℕ) : ℝ :=
  (N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ))

noncomputable def chenAPLogScale (N r : ℕ) : ℝ :=
  (N:ℝ)/((r.totient:ℝ)*Real.log (N:ℝ)^2)

private theorem eventually_log_sq_div_rpow_lt {α c : ℝ} (hα : 0<α) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, Real.log (N:ℝ)^2/(N:ℝ)^α < c := by
  have hg := (isLittleO_log_rpow_rpow_atTop (2:ℝ) hα).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h : Tendsto (fun N : ℕ => Real.log (N:ℝ)^2/(N:ℝ)^α) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using hg
  exact h.eventually_lt_const hc

/-- The same elementary switching error is negligible uniformly in the
progression modulus as long as its exponent is strictly below one eighth. -/
theorem chenAP_power_error_eventually_le {δ ε : ℝ} (hδ : δ<1/8) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ →
      2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ) ≤ ε*chenAPLogScale N r := by
  let α := (1/8:ℝ)-δ
  have hα : 0<α := sub_pos.mpr hδ
  filter_upwards [eventually_log_sq_div_rpow_lt hα (show 0<ε/3 by positivity),
    eventually_ge_atTop (2:ℕ)] with N h hN r hr hrN
  have hNr : (2:ℝ)≤N := Nat.cast_le.mpr hN
  have hNp : (0:ℝ)<N := by linarith
  have hN₁ : (1:ℝ)≤N := by linarith
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hp : (r.totient:ℝ)≤(N:ℝ)^δ :=
    (Nat.cast_le.mpr (Nat.totient_le r)).trans hrN
  have hpow : (N:ℝ)^(1/3:ℝ)≤(N:ℝ)^(7/8:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN₁ (by norm_num)
  have hsmall : 3*Real.log (N:ℝ)^2 ≤ ε*(N:ℝ)^α := by
    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos hNp _)).mp h
    linarith only [hh]
  unfold chenAPLogScale
  rw [←mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hφ (sq_pos_of_pos hL))).mpr
  calc
    _ ≤ (3*(N:ℝ)^(7/8:ℝ))*((N:ℝ)^δ*Real.log (N:ℝ)^2) := by
      apply mul_le_mul (by linarith only [hpow]) _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    _ = (3*Real.log (N:ℝ)^2)*(N:ℝ)^((7/8:ℝ)+δ) := by rw [Real.rpow_add hNp]; ring
    _ ≤ (ε*(N:ℝ)^α)*(N:ℝ)^((7/8:ℝ)+δ) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = _ := by
      rw [mul_assoc,←Real.rpow_add hNp,show α+(7/8+δ)=1 by dsimp [α]; ring,Real.rpow_one]

/-- The expected progression count tends to infinity uniformly in any
fixed polynomial range strictly smaller than the size of the interval. -/
theorem chenAPLogScale_eventually_gt {δ c : ℝ} (hδ : δ<1) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∀ r : ℕ, 0<r → (r:ℝ)≤(N:ℝ)^δ → c<chenAPLogScale N r := by
  have hα : 0<1-δ := sub_pos.mpr hδ
  filter_upwards [eventually_log_sq_div_rpow_lt hα (inv_pos.mpr hc),
    eventually_ge_atTop (2:ℕ)] with N h hN r hr hrN
  have hNr : (2:ℝ)≤N := Nat.cast_le.mpr hN
  have hNp : (0:ℝ)<N := by linarith
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hp : (r.totient:ℝ)≤(N:ℝ)^δ :=
    (Nat.cast_le.mpr (Nat.totient_le r)).trans hrN
  have hs : c*Real.log (N:ℝ)^2 < (N:ℝ)^(1-δ) := by
    have h₀ := (div_lt_iff₀ (Real.rpow_pos_of_pos hNp _)).mp h
    rw [mul_comm _ ((N:ℝ)^(1-δ)),←div_eq_mul_inv] at h₀
    exact (lt_div_iff₀' hc).mp h₀
  unfold chenAPLogScale
  apply (lt_div_iff₀ (mul_pos hφ (sq_pos_of_pos hL))).mpr
  calc
    _ ≤ c*((N:ℝ)^δ*Real.log (N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) hc.le
    _ = (c*Real.log (N:ℝ)^2)*(N:ℝ)^δ := by ring
    _ < (N:ℝ)^(1-δ)*(N:ℝ)^δ := mul_lt_mul_of_pos_right hs (by positivity)
    _ = _ := by rw [←Real.rpow_add hNp,sub_add_cancel,Real.rpow_one]

end FareyGoldbach
