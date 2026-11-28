import FareyGoldbach.DoubleAverageGoldbach

open scoped BigOperators Classical

namespace FareyGoldbach

/-- The discrepancy between the smoothed prime sum and the Route A model. -/
noncomputable def routeARemainder (r b Y : ℕ) (α : ℝ) : ℂ :=
  smoothedPrimeSum r b Y α - modelSum r b Y (routeAQ Y r) (routeAQ Y r) α

private theorem sa_prime_bounded (r b Y : ℕ) :
    ∃ B : ℝ, ∀ α, ‖smoothedPrimeSum r b Y α‖ ≤ B := by
  refine ⟨∑ j ∈ Finset.range (Y / r + 1),
    |quarticBump ((r * j + b : ℝ) / Y) * primeWeight (r * j + b)|, fun α => ?_⟩
  unfold smoothedPrimeSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]

theorem routeARemainder_measurable (r b Y : ℕ) :
    Measurable (routeARemainder r b Y) :=
  (continuous_smoothedPrimeSum r b Y).measurable.sub (modelSum_measurable ..)

theorem routeARemainder_bounded (r b Y : ℕ) : ∃ B : ℝ, ∀ α, ‖routeARemainder r b Y α‖ ≤ B := by
  obtain ⟨B, hB⟩ := sa_prime_bounded r b Y
  obtain ⟨M, hM⟩ := modelSum_norm_bounded r b Y (routeAQ Y r) (routeAQ Y r)
  exact ⟨B + M, fun α => (norm_sub_le _ _).trans (add_le_add (hB α) (hM α))⟩

private theorem sa_sq_int {f : ℝ → ℂ} (hf : Measurable f)
    (hb : ∃ B : ℝ, ∀ α, ‖f α‖ ≤ B) :
    IntervalIntegrable (fun α => ‖f α‖ ^ 2) MeasureTheory.volume 0 1 := by
  obtain ⟨B, hB⟩ := hb
  refine intervalIntegrable_of_measurable_bounded (B := B ^ 2)
    ((continuous_norm.measurable.comp hf).pow_const 2) fun α => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hB α) 2

private theorem sa_mul_bounded {f g : ℝ → ℂ} (hf : ∃ B : ℝ, ∀ α, ‖f α‖ ≤ B)
    (hg : ∃ B : ℝ, ∀ α, ‖g α‖ ≤ B) : ∃ B : ℝ, ∀ α, ‖f α * g α‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨D, hD⟩ := hg
  refine ⟨B * D, fun α => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hB α) (hD α) (norm_nonneg _) ((norm_nonneg _).trans (hB α))

private theorem sa_add_bounded {f g : ℝ → ℂ} (hf : ∃ B : ℝ, ∀ α, ‖f α‖ ≤ B)
    (hg : ∃ B : ℝ, ∀ α, ‖g α‖ ≤ B) : ∃ B : ℝ, ∀ α, ‖f α + g α‖ ≤ B := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨D, hD⟩ := hg
  exact ⟨B + D, fun α => (norm_add_le _ _).trans (add_le_add (hB α) (hD α))⟩

private theorem sa_integral_add_sq_le {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ B : ℝ, ∀ α, ‖f α‖ ≤ B) (hgb : ∃ B : ℝ, ∀ α, ‖g α‖ ≤ B) :
    (∫ α in (0 : ℝ)..1, ‖f α + g α‖ ^ 2) ≤
      2 * (∫ α in (0 : ℝ)..1, ‖f α‖ ^ 2) + 2 * (∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2) := by
  have hi := sa_sq_int hf hfb
  have hj := sa_sq_int hg hgb
  have h := intervalIntegral.integral_mono_on zero_le_one
    (sa_sq_int (hf.add hg) (sa_add_bounded hfb hgb))
    ((hi.const_mul (2 : ℝ)).add (hj.const_mul (2 : ℝ))) (fun α _ => by
      have htri := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f α) (g α)) 2
      have hsq : (‖f α‖ + ‖g α‖) ^ 2 ≤ 2 * ‖f α‖ ^ 2 + 2 * ‖g α‖ ^ 2 := by
        nlinarith only [sq_nonneg (‖f α‖ - ‖g α‖)]
      exact htri.trans hsq)
  rwa [intervalIntegral.integral_add (hi.const_mul _) (hj.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h

private theorem sa_mul_sq_int {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ B : ℝ, ∀ α, ‖f α‖ ≤ B) (hgb : ∃ B : ℝ, ∀ α, ‖g α‖ ≤ B) :
    IntervalIntegrable (fun α => ‖f α‖ ^ 2 * ‖g α‖ ^ 2) MeasureTheory.volume 0 1 := by
  simpa only [Pi.mul_apply, norm_mul, mul_pow] using sa_sq_int (hf.mul hg) (sa_mul_bounded hfb hgb)

theorem routeA_dyadic_pair_split {Y r : ℕ} (hr : 0 < r) (hH26 : 2 ^ 26 ≤ Y / r)
    (b₁ b₂ : {b // b ∈ coprimeClasses r}) :
    let Q := routeAQ Y r
    let thresh : ℝ := (1 / 262144) * ((r : ℝ) / (r.totient : ℝ))^2 * ((Y : ℝ) / (r : ℝ))
    ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1, (mem_coprimeClasses.mp b₁.2).1,
      (mem_coprimeClasses.mp b₂.2).1, (mem_coprimeClasses.mp b₁.2).2,
      (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ) * thresh ^ 2 ≤
      2 * (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b₁.1 Y α‖ ^ 2 *
        ‖routeARemainder r b₂.1 Y α‖ ^ 2) +
      2 * (∫ α in (0 : ℝ)..1, ‖routeARemainder r b₁.1 Y α‖ ^ 2 *
        ‖modelSum r b₂.1 Y Q Q α‖ ^ 2) := by
  dsimp only
  refine (routeA_dyadic_pair_bessel hr hH26 b₁ b₂).trans ?_
  set Q := routeAQ Y r
  let S₁ := smoothedPrimeSum r b₁.1 Y
  let S₂ := smoothedPrimeSum r b₂.1 Y
  let M₁ := modelSum r b₁.1 Y Q Q
  let M₂ := modelSum r b₂.1 Y Q Q
  let R₁ := routeARemainder r b₁.1 Y
  let R₂ := routeARemainder r b₂.1 Y
  change (∫ α in (0 : ℝ)..1, ‖S₁ α * S₂ α - M₁ α * M₂ α‖ ^ 2) ≤
    2 * (∫ α in (0 : ℝ)..1, ‖S₁ α‖ ^ 2 * ‖R₂ α‖ ^ 2) +
    2 * (∫ α in (0 : ℝ)..1, ‖R₁ α‖ ^ 2 * ‖M₂ α‖ ^ 2)
  have hf : Measurable (fun α => S₁ α * R₂ α) :=
    (continuous_smoothedPrimeSum ..).measurable.mul (routeARemainder_measurable ..)
  have hg : Measurable (fun α => R₁ α * M₂ α) :=
    (routeARemainder_measurable ..).mul (modelSum_measurable ..)
  have hid (α : ℝ) : S₁ α * S₂ α - M₁ α * M₂ α =
      S₁ α * R₂ α + R₁ α * M₂ α := by
    change S₁ α * S₂ α - M₁ α * M₂ α = S₁ α * (S₂ α - M₂ α) + (S₁ α - M₁ α) * M₂ α
    ring
  simp only [hid]
  simpa only [norm_mul, mul_pow] using sa_integral_add_sq_le hf hg
    (sa_mul_bounded (sa_prime_bounded ..) (routeARemainder_bounded ..))
    (sa_mul_bounded (routeARemainder_bounded ..) (modelSum_norm_bounded ..))

theorem routeA_fixed_l2 {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r b Y : ℕ} (hr : 0 < r) (hb : b < r) (hbr : Nat.Coprime b r)
    (hH : 2 ^ 72 ≤ Y / r)
    (hB : ((r.totient : ℝ) / r)^2 * (r : ℝ) * Real.log (2 * (Y : ℝ))^2 ≤ (Y : ℝ) / r) :
    let H : ℝ := (Y : ℝ) / r
    let κ : ℝ := (r : ℝ) / r.totient
    let L := Real.log (2 * (Y : ℝ))
    (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) ≤ (1 + 2 * C) * κ * H * L ∧
    (∫ α in (0 : ℝ)..1, ‖routeARemainder r b Y α‖ ^ 2) ≤ (74 + 4 * C) * κ * H * L := by
  dsimp only
  have hH26 : 2 ^ 26 ≤ Y / r := le_trans (by norm_num) hH
  have hrY : r ≤ Y := by
    simpa using (Nat.mul_le_mul_left r (show 1 ≤ Y / r by omega)).trans (Nat.mul_div_le Y r)
  have hY72 : 2 ^ 72 ≤ Y := by
    simpa using (Nat.mul_le_mul hr hH).trans (Nat.mul_div_le Y r)
  have hY2 : 2 ≤ Y := by omega
  obtain ⟨_, _, _, hQ_le_Y⟩ := routeAQ_bounds hr hH26
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have ht' : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  set H : ℝ := (Y : ℝ) / r
  set κ : ℝ := (r : ℝ) / r.totient
  set L := Real.log (2 * (Y : ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * Y))
  have hκ : 0 < κ := div_pos hr' ht'
  have hB' : (Y : ℝ) * L^2 ≤ (κ * H)^2 := by
    have h := mul_le_mul_of_nonneg_left hB (mul_nonneg (show 0 ≤ H by positivity) (sq_nonneg κ))
    convert h using 1 <;> dsimp [L, H, κ] <;> field_simp
  have hroot : Real.sqrt Y * L ≤ κ * H := by
    have heq : (Real.sqrt (Y : ℝ) * L)^2 = (Y : ℝ) * L^2 := by
      rw [mul_pow, Real.sq_sqrt hY'.le]
    rw [← heq] at hB'
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hB'
  have hS : (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) ≤
      (1 + 2 * C) * κ * H * L := by
    refine (smoothedPrimeSum_l2_le hC hTw hr hrY hY2 hb hbr).trans ?_
    have h := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 2 * C by positivity)
    have h' := mul_le_mul_of_nonneg_right (add_le_add_left h (κ * H)) hL
    convert h' using 1 <;> ring
  refine ⟨hS, ?_⟩
  have hM := modelSum_l2_le (b := b) (Q := routeAQ Y r) hr hrY hQ_le_Y hY72
  have hh := sa_integral_add_sq_le (continuous_smoothedPrimeSum r b Y).measurable
    (modelSum_measurable r b Y (routeAQ Y r) (routeAQ Y r)).neg
    (sa_prime_bounded r b Y) (by
      obtain ⟨B, h⟩ := modelSum_norm_bounded r b Y (routeAQ Y r) (routeAQ Y r)
      exact ⟨B, fun α => by simpa only [Pi.neg_apply, norm_neg] using h α⟩)
  have hh' : (∫ α in (0 : ℝ)..1, ‖routeARemainder r b Y α‖ ^ 2) ≤
      2 * (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) +
      2 * (∫ α in (0 : ℝ)..1, ‖modelSum r b Y (routeAQ Y r) (routeAQ Y r) α‖ ^ 2) := by
    simpa only [routeARemainder, sub_eq_add_neg, Pi.neg_apply, norm_neg] using hh
  refine hh'.trans ((add_le_add (mul_le_mul_of_nonneg_left hS (by norm_num))
    (mul_le_mul_of_nonneg_left hM (by norm_num))).trans_eq ?_)
  change 2 * ((1 + 2 * C) * κ * H * L) + 2 * (36 * κ * H * L) = _
  ring

theorem routeA_first_energy {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r b Y : ℕ} (hr : 0 < r) (hb : b < r) (hbr : Nat.Coprime b r)
    (hH : 2 ^ 72 ≤ Y / r)
    (hB : ((r.totient : ℝ) / r)^2 * (r : ℝ) * Real.log (2 * (Y : ℝ))^2 ≤ (Y : ℝ) / r) :
    let H : ℝ := (Y : ℝ) / r
    let κ : ℝ := (r : ℝ) / r.totient
    let L := Real.log (2 * (Y : ℝ))
    (1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r,
      (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖^2 * ‖routeARemainder r b₂ Y α‖^2) ≤
    ((3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39) * (1 + 2 * C)) *
      (κ^2 * H^2 * Real.sqrt H * L^3) := by
  dsimp only
  have hH26 : 2 ^ 26 ≤ Y / r := le_trans (by norm_num) hH
  have hrY : r ≤ Y := by
    simpa using (Nat.mul_le_mul_left r (show 1 ≤ Y / r by omega)).trans (Nat.mul_div_le Y r)
  have hY2 : 2 ≤ Y := by
    have h := (Nat.mul_le_mul hr hH).trans (Nat.mul_div_le Y r)
    omega
  let S := smoothedPrimeSum r b Y
  let R := fun b₂ => routeARemainder r b₂ Y
  set H : ℝ := (Y : ℝ) / r
  set κ : ℝ := (r : ℝ) / r.totient
  set L := Real.log (2 * (Y : ℝ))
  set C₁ : ℝ := 3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39
  set M := C₁ * κ * H * Real.sqrt H * L^2
  have hM : 0 ≤ M := by dsimp [M, C₁, κ, H]; positivity
  have hi : ∀ b₂, IntervalIntegrable (fun α => ‖S α‖ ^ 2 * ‖R b₂ α‖ ^ 2)
      MeasureTheory.volume 0 1 :=
    fun b₂ => sa_mul_sq_int (continuous_smoothedPrimeSum r b Y).measurable
      (routeARemainder_measurable r b₂ Y) (sa_prime_bounded r b Y)
      (routeARemainder_bounded r b₂ Y)
  have hs := sa_sq_int (continuous_smoothedPrimeSum r b Y).measurable (sa_prime_bounded r b Y)
  calc (1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r,
        (∫ α in (0 : ℝ)..1, ‖S α‖ ^ 2 * ‖R b₂ α‖ ^ 2)
      = ∫ α in (0 : ℝ)..1, (1 / (r.totient : ℝ)) *
          ∑ b₂ ∈ coprimeClasses r, ‖S α‖ ^ 2 * ‖R b₂ α‖ ^ 2 := by
          rw [← intervalIntegral_finset_sum (fun b₂ _ => hi b₂), intervalIntegral.integral_const_mul]
    _ ≤ ∫ α in (0 : ℝ)..1, M * ‖S α‖ ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((intervalIntegrable_finset_sum _ fun b₂ _ => hi b₂).const_mul _) (hs.const_mul M) ?_
        intro α _
        rw [← Finset.mul_sum]
        have ha := avg_remainder_sq hC hTw hr hrY hH26 α
        change (1 / (r.totient : ℝ)) * (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖^2) ≤ M at ha
        calc _ = ((1 / (r.totient : ℝ)) *
            (∑ b₂ ∈ coprimeClasses r, ‖R b₂ α‖^2)) * ‖S α‖^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
    _ = M * (∫ α in (0 : ℝ)..1, ‖S α‖ ^ 2) := intervalIntegral.integral_const_mul _ _
    _ ≤ M * ((1 + 2 * C) * κ * H * L) :=
      mul_le_mul_of_nonneg_left (routeA_fixed_l2 hC hTw hr hb hbr hH hB).1 hM
    _ = _ := by dsimp [M]; ring

end FareyGoldbach
