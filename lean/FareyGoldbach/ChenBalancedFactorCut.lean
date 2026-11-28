import FareyGoldbach.ChenAPScale

/-! # The power inequality for the smaller prime factor below the balanced cutoff -/

namespace FareyGoldbach

/-- When `u*v` exceeds the short initial segment and `u` lies below the
balanced cutoff, the ratio of the logarithmic exponents bounds the two factors. -/
theorem chen_bounded_factor_of_cut {N u v : ℕ} {η ε α : ℝ} (hN : 1≤N)
    (hεη : ε<η) (hα : 1<α)
    (hratio : (1/2-η)/(1/2+η-ε)≤α-1)
    (hprod : chenPowerLevel (1-ε) N < u*v) (hu : u≤chenPowerLevel (1/2-η) N) :
    (u:ℝ) ≤ (v:ℝ)^(α-1) := by
  have hn : 1≤(N:ℝ) := Nat.one_le_cast.mpr hN
  have hn₀ : 0<(N:ℝ) := zero_lt_one.trans_le hn
  have hbase : 0<(1/2+η-ε) := by linarith only [hεη]
  have hul : (u:ℝ)≤(N:ℝ)^(1/2-η) :=
    (Nat.cast_le.mpr hu).trans (Nat.floor_le (by positivity))
  have hgt : (N:ℝ)^(1-ε)<(u:ℝ)*(v:ℝ) := by
    have hp : (chenPowerLevel (1-ε) N:ℝ)+1≤(u:ℝ)*(v:ℝ) := by exact_mod_cast hprod
    exact (Nat.lt_floor_add_one ((N:ℝ)^(1-ε))).trans_le hp
  have hvl : (N:ℝ)^(1/2+η-ε)≤(v:ℝ) := by
    by_contra! hh
    have hle := mul_le_mul hul hh.le (Nat.cast_nonneg v) (Real.rpow_nonneg hn₀.le _)
    rw [←Real.rpow_add hn₀,show 1/2-η+(1/2+η-ε)=1-ε by ring] at hle
    exact hgt.not_ge hle
  have hexp := (div_le_iff₀ hbase).mp hratio
  calc
    (u:ℝ) ≤ (N:ℝ)^(1/2-η) := hul
    _ ≤ (N:ℝ)^((1/2+η-ε)*(α-1)) := Real.rpow_le_rpow_of_exponent_le hn
      (by simpa only [mul_comm] using hexp)
    _ = ((N:ℝ)^(1/2+η-ε))^(α-1) := Real.rpow_mul hn₀.le _ _
    _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hn₀.le _) hvl (sub_nonneg.mpr hα.le)

end FareyGoldbach
