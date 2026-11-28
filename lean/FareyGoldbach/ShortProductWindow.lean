import FareyGoldbach.ShortDoubleAverageGoldbach

/-! # Global product energy and the Farey coefficient at a bad frequency -/

open MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

/-- Ordinary Bessel on any finite window, for the product of two bounded periodic functions. -/
theorem productWindowEnergy_le_integral (u v : BoundedPeriodicFunction) (m K : ℕ) :
    productWindowEnergy u v m K ≤ ∫ x in (0:ℝ)..1, ‖u x * v x‖^2 := by
  obtain ⟨B,hB⟩ := u.bounded
  obtain ⟨D,hD⟩ := v.bounded
  have hb (x : ℝ) : ‖u x*v x‖ ≤ B*D := by
    rw [norm_mul]
    exact mul_le_mul (hB x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
  have hsub : Finset.Icc m (m+K) ⊆ Finset.range (m+K+1) := by
    exact fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
  exact (Finset.sum_le_sum_of_subset_of_nonneg (f:=fun k : ℕ =>
    ‖shortFourierCoeff (fun x => u x*v x) k‖^2) hsub fun _ _ _ => sq_nonneg _).trans
    (bessel_intervalIntegral (u.measurable.mul v.measurable) hb _)

/-- The continuous model coefficient is uniformly positive on every exceptional frequency
in the common translated window. -/
theorem short_model_bad_freq_lower_progressions (P : Progressions) {X Δ : ℕ}
    (hrX : P.r ≤ X) (hΔX : Δ ≤ X) (hbig : 2^72 ≤ Δ/P.r) {k : ℕ}
    (hk : k ∈ shortBadFrequencies P X Δ) :
    (1:ℝ)/262144*((P.r:ℝ)/P.r.totient)^2*(((X+Δ:ℕ):ℝ)/P.r) ≤
      (shortFourierCoeff (fun x => shortContModel P.r P.b₁ (X+Δ) (routeAQ Δ P.r) x *
        shortContModel P.r P.b₂ (X+Δ) (routeAQ Δ P.r) x) k).re := by
  have hr := P.r_pos
  have hr' : (0:ℝ)<P.r := Nat.cast_pos.mpr hr
  have hk0 : 0≤(Δ:ℝ)/P.r := by positivity
  obtain ⟨hQ2,_,hQhi,_⟩ := routeAQ_bounds hr (le_trans (by norm_num : 2^26 ≤ 2^72) hbig)
  have hsmall : (2:ℝ)^24*(routeAQ Δ P.r:ℝ)^2 ≤ ((X+Δ:ℕ):ℝ)/P.r := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg _) hQhi 2
    rw [mul_pow,Real.sq_sqrt hk0] at hs
    have hd : (Δ:ℝ)/P.r ≤ ((X+Δ:ℕ):ℝ)/P.r :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_left Δ X) hr'.le
    norm_num at hs hd ⊢; linarith
  obtain ⟨n,hn,hk'⟩ := Finset.mem_image.mp hk
  have hrec := shortBadFrequencies_recover P hrX hn
  rw [hk'] at hrec
  obtain ⟨hlo,hhi,hev,_,_⟩ := shortIntervalExceptions_mem hn
  have hy : (X+Δ)/2 < n := by omega
  exact shortContModel_conv_re_lower hr P.b₁_lt P.b₂_lt (hrec ▸ hy) (hrec ▸ hhi)
    (hrec ▸ hev) hQ2 hsmall

theorem short_model_bad_freq_lower {X Δ r : ℕ} (hr : 0<r) (_hX : 2≤X) (hrX : r≤X)
    (_hΔ : 1≤Δ) (hΔX : Δ≤X) (hbig : 2^72≤Δ/r)
    (b c : {b // b ∈ coprimeClasses r}) {k : ℕ}
    (hk : k ∈ shortBadFrequencies (shortProgressions hr b c) X Δ) :
    (1:ℝ)/262144*((r:ℝ)/r.totient)^2*(((X+Δ:ℕ):ℝ)/r) ≤
      (shortFourierCoeff (fun x => shortContModel r b.1 (X+Δ) (routeAQ Δ r) x *
        shortContModel r c.1 (X+Δ) (routeAQ Δ r) x) k).re :=
  short_model_bad_freq_lower_progressions (shortProgressions hr b c) hrX hΔX hbig hk

end FareyGoldbach
