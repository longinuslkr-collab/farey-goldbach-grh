import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import FareyGoldbach.VoronoiCells
import FareyGoldbach.SingularSeries
import FareyGoldbach.PrimeSums
import FareyGoldbach.ModelAndRemainder

/-!
# Modules D & E: Bessel Inequality, Dyadic Counting, and Stage-1 Closure (`SmoothedTwistEstimate → Target`)

This module closes **Stage 1** of the Lean 4 formalization with zero `sorry`:
1. **Module D1**:
   - `integral_smoothedPrimeSum_mul_e`: exact Fourier coefficient of `S_{b₁} * S_{b₂}`.
   - `primeConvolution_eq_zero_of_exception`: every exception gives vanishing prime convolution.
   - `bessel_intervalIntegral`: finite Bessel inequality on `[0, 1]`.
2. **Module D2 (`dyadicBound_of_smoothedTwistEstimate`)**:
   - Combines the main Farey regime (`r^5 ≤ Y^2`, `Y ≥ Y₀`), the large-modulus trivial
     congruence regime (`Y^2 < r^5`), and the finite small-`Y` regime (`Y < Y₀`).
3. **Module E (`target_of_dyadicBound`, `target_of_smoothedTwistEstimate`)**:
   - Dyadic summation from `r` to `X` plus trivial congruence bound `2 * X / r`.
-/

open scoped BigOperators

namespace FareyGoldbach

section BesselAndPrimeConv

/-- Exact Fourier coefficient of `smoothedPrimeSum r b₁ Y * smoothedPrimeSum r b₂ Y` at frequency `k`. -/
lemma integral_smoothedPrimeSum_mul_e {r b₁ b₂ Y k : ℕ} (hk : k ≤ Y / r) :
    (∫ α in (0 : ℝ)..1,
      smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α * e (-((k : ℝ) * α))) =
      ((∑ j₁ ∈ Finset.range (k + 1),
        (quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁)) *
        (quarticBump (((r * (k - j₁) + b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * (k - j₁) + b₂)) : ℝ) : ℂ) := by
  have hpt : ∀ α : ℝ,
      smoothedPrimeSum r b₁ Y α * smoothedPrimeSum r b₂ Y α * e (-((k : ℝ) * α)) =
      ∑ j₁ ∈ Finset.range (Y / r + 1), ∑ j₂ ∈ Finset.range (Y / r + 1),
        (((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁)) *
          (quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₂ + b₂)) : ℝ) : ℂ) *
          e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    unfold smoothedPrimeSum
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    have hexp : e (α * (j₁ : ℝ)) * e (α * (j₂ : ℝ)) * e (-((k : ℝ) * α)) =
        e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) := by
      rw [← e_add, ← e_add]; congr 1; push_cast; ring
    calc ((quarticBump ((r * j₁ + b₁ : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁) : ℝ) : ℂ) * e (α * (j₁ : ℝ)) *
          (((quarticBump ((r * j₂ + b₂ : ℝ) / (Y : ℝ)) * primeWeight (r * j₂ + b₂) : ℝ) : ℂ) * e (α * (j₂ : ℝ))) *
          e (-((k : ℝ) * α))
        = (((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁)) *
            (quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₂ + b₂)) : ℝ) : ℂ) *
            (e (α * (j₁ : ℝ)) * e (α * (j₂ : ℝ)) * e (-((k : ℝ) * α))) := by push_cast; ring
      _ = _ := by rw [hexp]
  simp_rw [hpt]
  rw [intervalIntegral_finset_sum]
  · have hinner : ∀ j₁ ∈ Finset.range (Y / r + 1),
        (∫ α in (0 : ℝ)..1, ∑ j₂ ∈ Finset.range (Y / r + 1),
          (((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁)) *
            (quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₂ + b₂)) : ℝ) : ℂ) *
            e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * α)) =
        ∑ j₂ ∈ Finset.range (Y / r + 1), ∫ α in (0 : ℝ)..1,
          (((quarticBump (((r * j₁ + b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₁ + b₁)) *
            (quarticBump (((r * j₂ + b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (r * j₂ + b₂)) : ℝ) : ℂ) *
            e ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) :=
      fun j₁ _ => intervalIntegral_finset_sum fun j₂ _ =>
        (continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1
    rw [Finset.sum_congr rfl hinner]
    simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
    rw [Complex.ofReal_sum]
    have hsub : Finset.range (k + 1) ⊆ Finset.range (Y / r + 1) := Finset.range_mono (by omega)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      have hj₁_le : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
      have hkj : k - j₁ ∈ Finset.range (Y / r + 1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single (k - j₁)]
      · have hz : (j₁ : ℤ) + ((k - j₁ : ℕ) : ℤ) - (k : ℤ) = 0 := by omega
        simp [hz]
      · intro j₂ _ hne
        have hnz : (j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [hnz]
      · intro h; exact absurd hkj h
    · intro j₁ _ hj₁_not
      have hj₁_gt : k < j₁ := by simpa [Finset.mem_range] using hj₁_not
      apply Finset.sum_eq_zero
      intro j₂ _
      have hnz : (j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) ≠ 0 := by omega
      simp [hnz]
  · intro j₁ _
    exact intervalIntegrable_finset_sum (Finset.range (Y / r + 1)) fun j₂ _ =>
      (continuous_const.mul (continuous_e_mul ((((j₁ : ℤ) + (j₂ : ℤ) - (k : ℤ) : ℤ) : ℝ)))).intervalIntegrable 0 1

/-- **Module D1a:** If `n = P.r * k + P.b₁ + P.b₂` has zero prime representations, then the
`k`-th Fourier coefficient of `smoothedPrimeSum₁ * smoothedPrimeSum₂` vanishes identically. -/
theorem primeConvolution_eq_zero_of_exception (P : Progressions) {Y k : ℕ}
    (hk : k ≤ Y / P.r) (hexc : (primeRepresentations P (P.r * k + P.b₁ + P.b₂)).card = 0) :
    (∫ α in (0 : ℝ)..1,
      smoothedPrimeSum P.r P.b₁ Y α * smoothedPrimeSum P.r P.b₂ Y α * e (-((k : ℝ) * α))) = 0 := by
  rw [integral_smoothedPrimeSum_mul_e hk]
  suffices h0 : ∑ j₁ ∈ Finset.range (k + 1),
      (quarticBump (((P.r * j₁ + P.b₁ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (P.r * j₁ + P.b₁)) *
      (quarticBump (((P.r * (k - j₁) + P.b₂ : ℕ) : ℝ) / (Y : ℝ)) * primeWeight (P.r * (k - j₁) + P.b₂)) = 0 by
    rw [h0, Complex.ofReal_zero]
  apply Finset.sum_eq_zero
  intro j₁ hj₁
  have hj₁_le : j₁ ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj₁)
  set p₁ := P.r * j₁ + P.b₁
  set p₂ := P.r * (k - j₁) + P.b₂
  by_cases hp1 : p₁.Prime
  · by_cases hp2 : p₂.Prime
    · exfalso
      have hsum : p₁ + p₂ = P.r * k + P.b₁ + P.b₂ := by
        dsimp [p₁, p₂]
        have : P.r * j₁ + P.r * (k - j₁) = P.r * k := by rw [← mul_add, Nat.add_sub_of_le hj₁_le]
        omega
      have hmem : (p₁, p₂) ∈ primeRepresentations P (P.r * k + P.b₁ + P.b₂) := by
        unfold primeRepresentations
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hp1, hp2, hsum, ?_, ?_⟩
        · exact Finset.mem_Icc.mpr ⟨hp1.two_le, by omega⟩
        · exact Finset.mem_Icc.mpr ⟨hp2.two_le, by omega⟩
        · dsimp [p₁]; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt P.b₁_lt]
        · dsimp [p₂]; rw [Nat.mul_add_mod, Nat.mod_eq_of_lt P.b₂_lt]
      have hpos : 0 < (primeRepresentations P (P.r * k + P.b₁ + P.b₂)).card :=
        Finset.card_pos.mpr ⟨(p₁, p₂), hmem⟩
      omega
    · simp [primeWeight, hp2]
  · simp [primeWeight, hp1]

/-- **Module D1b (Finite Bessel inequality on `[0, 1]`):**
For any bounded measurable `F : ℝ → ℂ` and any `M : ℕ`,
`∑_{k < M} ‖∫_0^1 F(α) e(-k α)‖² ≤ ∫_0^1 ‖F(α)‖²`. -/
theorem bessel_intervalIntegral {F : ℝ → ℂ} (hmeas : Measurable F) {B : ℝ}
    (hB : ∀ α, ‖F α‖ ≤ B) (M : ℕ) :
    ∑ k ∈ Finset.range M, ‖∫ α in (0 : ℝ)..1, F α * e (-((k : ℝ) * α))‖ ^ 2 ≤
      ∫ α in (0 : ℝ)..1, ‖F α‖ ^ 2 := by
  let c : ℕ → ℂ := fun k => ∫ α in (0 : ℝ)..1, F α * e (-((k : ℝ) * α))
  let G : ℝ → ℂ := fun α => ∑ k ∈ Finset.range M, c k * e (α * (k : ℝ))
  have hG_cont : Continuous G := by
    dsimp [G]
    refine continuous_sum_finset _ fun k _ => ?_
    have h : (fun α : ℝ => c k * e (α * (k : ℝ))) = fun α : ℝ => c k * e ((k : ℝ) * α) := by
      funext α; rw [mul_comm α]
    rw [h]
    exact continuous_const.mul (continuous_e_mul (k : ℝ))
  have hG_bound : ∃ BG : ℝ, ∀ α, ‖G α‖ ≤ BG := by
    refine ⟨∑ k ∈ Finset.range M, ‖c k‖, fun α => ?_⟩
    dsimp [G]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_e, mul_one]
  obtain ⟨BG, hBG⟩ := hG_bound
  have hB_nn : 0 ≤ B := (norm_nonneg (F 0)).trans (hB 0)
  have hBG_nn : 0 ≤ BG := (norm_nonneg (G 0)).trans (hBG 0)
  have hF2_int : IntervalIntegrable (fun α => ‖F α‖ ^ 2) MeasureTheory.volume 0 1 := by
    refine intervalIntegrable_of_measurable_bounded (B := B ^ 2)
      ((continuous_norm.measurable.comp hmeas).pow_const 2) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB α) 2
  have hG2_int : IntervalIntegrable (fun α => ‖G α‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((continuous_norm.comp hG_cont).pow 2).intervalIntegrable 0 1
  have hFG_int : IntervalIntegrable (fun α => F α * star (G α)) MeasureTheory.volume 0 1 := by
    have hm : Measurable (fun α => F α * star (G α)) :=
      hmeas.mul (continuous_star.measurable.comp hG_cont.measurable)
    refine intervalIntegrable_of_measurable_bounded (B := B * BG) hm fun α => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hB α) (hBG α) (norm_nonneg _) hB_nn
  have hcross_int : IntervalIntegrable (fun α => 2 * (F α * star (G α)).re) MeasureTheory.volume 0 1 := by
    have hre_meas : Measurable (fun α => (F α * star (G α)).re) :=
      Complex.continuous_re.measurable.comp (hmeas.mul (continuous_star.measurable.comp hG_cont.measurable))
    have hre_int : IntervalIntegrable (fun α => (F α * star (G α)).re) MeasureTheory.volume 0 1 := by
      refine intervalIntegrable_of_measurable_bounded (B := B * BG) hre_meas fun α => ?_
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hB α) (hBG α) (norm_nonneg _) hB_nn)
    exact hre_int.const_mul 2
  -- Expand `0 ≤ ∫_0^1 ‖F α - G α‖²`.
  have hpt : ∀ α : ℝ, ‖F α - G α‖ ^ 2 = ‖F α‖ ^ 2 - 2 * (F α * star (G α)).re + ‖G α‖ ^ 2 := by
    intro α
    have hC : ((‖F α - G α‖ ^ 2 : ℝ) : ℂ) =
        ((‖F α‖ ^ 2 : ℝ) : ℂ) - F α * star (G α) - star (F α * star (G α)) + ((‖G α‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, Complex.ofReal_pow, Complex.ofReal_pow,
          ← Complex.mul_conj', ← Complex.mul_conj', ← Complex.mul_conj',
          ← Complex.star_def, star_sub, star_mul', star_star]
      ring
    have hre := congrArg Complex.re hC
    simp only [Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.star_def, Complex.conj_re] at hre
    rw [← Complex.star_def] at hre
    linarith
  have hnn : 0 ≤ ∫ α in (0 : ℝ)..1, ‖F α - G α‖ ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun α _ => sq_nonneg _
  simp_rw [hpt] at hnn
  rw [intervalIntegral.integral_add (hF2_int.sub hcross_int) hG2_int,
      intervalIntegral.integral_sub hF2_int hcross_int] at hnn
  -- Evaluate `∫_0^1 ‖G α‖² = ∑_{k < M} ‖c k‖²` via `integral_norm_sq_trigPoly`.
  have hG2_eq : (∫ α in (0 : ℝ)..1, ‖G α‖ ^ 2) = ∑ k ∈ Finset.range M, ‖c k‖ ^ 2 :=
    integral_norm_sq_trigPoly M c
  -- Evaluate `∫_0^1 2 * (F α * star (G α)).re = 2 * ∑_{k < M} ‖c k‖²`.
  have hcross_eq : (∫ α in (0 : ℝ)..1, 2 * (F α * star (G α)).re) = 2 * ∑ k ∈ Finset.range M, ‖c k‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hre_comm : (∫ α in (0 : ℝ)..1, (F α * star (G α)).re) =
        (∫ α in (0 : ℝ)..1, F α * star (G α)).re :=
      Complex.reCLM.intervalIntegral_comp_comm hFG_int
    rw [hre_comm]
    have hFG_sum : ∀ α : ℝ, F α * star (G α) =
        ∑ k ∈ Finset.range M, star (c k) * (F α * e (-((k : ℝ) * α))) := by
      intro α
      dsimp [G]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      have hstar_e : (starRingEnd ℂ) (e (α * (k : ℝ))) = e (-((k : ℝ) * α)) := by
        rw [← Complex.star_def]
        apply mul_left_cancel₀ (show e (α * (k : ℝ)) ≠ 0 from by unfold e; exact Complex.exp_ne_zero _)
        rw [e_mul_star_e, ← e_add]
        have : α * (k : ℝ) + -((k : ℝ) * α) = 0 := by ring
        rw [this, e_zero]
      rw [hstar_e]; ring
    simp_rw [hFG_sum]
    have hint_k : ∀ k ∈ Finset.range M,
        IntervalIntegrable (fun α => star (c k) * (F α * e (-((k : ℝ) * α)))) MeasureTheory.volume 0 1 := by
      intro k _
      have he_meas : Measurable (fun α : ℝ => e (-((k : ℝ) * α))) := by
        have h : (fun α : ℝ => e (-((k : ℝ) * α))) = fun α : ℝ => e (-(k : ℝ) * α) := by funext α; ring_nf
        rw [h]; exact (continuous_e_mul (-(k : ℝ))).measurable
      have hm : Measurable (fun α => star (c k) * (F α * e (-((k : ℝ) * α)))) :=
        measurable_const.mul (hmeas.mul he_meas)
      refine intervalIntegrable_of_measurable_bounded (B := ‖c k‖ * B) hm fun α => ?_
      rw [norm_mul, norm_star, norm_mul, norm_e, mul_one]
      exact mul_le_mul_of_nonneg_left (hB α) (norm_nonneg _)
    rw [intervalIntegral_finset_sum hint_k]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    change (star (c k) * c k).re = ‖c k‖ ^ 2
    rw [mul_comm, Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  linarith [hnn, hG2_eq, hcross_eq]

end BesselAndPrimeConv

section DyadicTheorem

/-- Elementary congruence-class count: at most `X / r + 1` integers in `Icc 1 X` satisfy `n % r = rem`. -/
lemma card_congruence_Icc_le (X r rem : ℕ) (_hr : 0 < r) :
    ((Finset.Icc 1 X).filter (fun n => n % r = rem)).card ≤ X / r + 1 := by
  let S := (Finset.Icc 1 X).filter (fun n => n % r = rem)
  have hsub : S.image (fun n => n / r) ⊆ Finset.range (X / r + 1) := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hnX : n ≤ X := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnX))
  have hinj : Set.InjOn (fun n : ℕ => n / r) (S : Set ℕ) := by
    intro n₁ h1 n₂ h2 hEq
    have hm1 : n₁ % r = rem := (Finset.mem_filter.mp h1).2
    have hm2 : n₂ % r = rem := (Finset.mem_filter.mp h2).2
    have hd1 := Nat.div_add_mod n₁ r
    have hd2 := Nat.div_add_mod n₂ r
    dsimp only at hEq
    rw [hEq, hm1] at hd1
    rw [hm2] at hd2
    omega
  rw [← Finset.card_image_of_injOn hinj]
  exact (Finset.card_le_card hsub).trans (by simp)

/-- Elementary `m / φ(m) ≤ 2^16 * m^(1/16)` for all `m ≥ 1`. -/
lemma div_totient_le_rpow_sixteenth (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) ≤ (2 : ℝ) ^ 16 * (m : ℝ) ^ ((1 : ℝ) / 16) := by
  rw [div_totient_eq_prod m hm]
  set P := m.primeFactors
  set P1 := P.filter (fun p => p < 16)
  set P2 := P.filter (fun p => ¬ (p < 16))
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 16)]
  have h1 : ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (2 : ℝ) ^ 16 := by
    have hcard : P1.card ≤ 16 := by
      have hsub : P1 ⊆ Finset.range 16 := fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ P1, (2 : ℝ) := by
          refine real_prod_le_prod P1 _ _ (fun p hp => ?_) (fun p hp => ?_)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            exact div_nonneg (by linarith) (by linarith)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            rw [div_le_iff₀ (by linarith)]; linarith
      _ = (2 : ℝ) ^ P1.card := by simp
      _ ≤ (2 : ℝ) ^ 16 := pow_le_pow_right₀ (by norm_num) hcard
  have h2 : ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (m : ℝ) ^ ((1 : ℝ) / 16) := by
    have h16 : (∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ 16 ≤ (m : ℝ) := by
      rw [← Finset.prod_pow]
      calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ^ 16
          ≤ ∏ p ∈ P2, (p : ℝ) := by
            refine real_prod_le_prod P2 _ _ (fun p hp => ?_) (fun p hp => ?_)
            · have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              exact pow_nonneg (div_nonneg (by linarith) (by linarith)) 16
            · have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              have hle : (p : ℝ) / ((p : ℝ) - 1) ≤ (16 : ℝ) / 15 := by
                rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
              calc ((p : ℝ) / ((p : ℝ) - 1)) ^ 16 ≤ ((16 : ℝ) / 15) ^ 16 :=
                    pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hle 16
                _ ≤ 16 := by norm_num
                _ ≤ (p : ℝ) := hp16
        _ = ((∏ p ∈ P2, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
        _ ≤ (m : ℝ) := by
            exact_mod_cast Nat.le_of_dvd hm
              ((Finset.prod_dvd_prod_of_subset P2 P id (Finset.filter_subset _ _)).trans
                (Nat.prod_primeFactors_dvd m))
    have hnn : 0 ≤ ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) :=
      Finset.prod_nonneg fun p hp => by
        have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
        exact div_nonneg (by linarith) (by linarith)
    calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))
        = ((∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_le_rpow (pow_nonneg hnn 16) h16 (by norm_num)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp => by
    have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
    exact div_nonneg (by linarith) (by linarith)) (by positivity)

/-- Elementary `log(2Y) ≤ 11 * Y^(1/10)` for `Y ≥ 1`. -/
lemma log_two_mul_le_rpow_tenth {Y : ℕ} (hY : 1 ≤ Y) :
    Real.log (2 * (Y : ℝ)) ≤ 11 * (Y : ℝ) ^ ((1 : ℝ) / 10) := by
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr hY
  have hY1 : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr hY
  have hY10 : (1 : ℝ) ≤ (Y : ℝ) ^ ((1 : ℝ) / 10) := Real.one_le_rpow hY1 (by norm_num)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogY : Real.log (Y : ℝ) ≤ 10 * (Y : ℝ) ^ ((1 : ℝ) / 10) := by
    have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hY_pos ((1 : ℝ) / 10))
    rw [Real.log_rpow hY_pos] at h1
    linarith
  rw [Real.log_mul (by norm_num) hY_pos.ne']
  linarith

private noncomputable def dyadicY0 : ℕ :=
  max (2 ^ 100) (Nat.ceil ((8 * rankinConst * (2 : ℝ) ^ 13) ^ ((80 : ℝ) / 7))) + 2 ^ 100

private lemma dyadic_main_regime_basic {r Y : ℕ} (hr : 0 < r)
    (hY_small : dyadicY0 ≤ Y) (hr_big : r ^ 5 ≤ Y ^ 2) :
    (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ (Y : ℝ) / (r : ℝ) ∧
    2 ^ 25 ≤ Nat.sqrt (Y / r) ∧
    Nat.sqrt (Y / r) / 2 ^ 24 ≤ Y ∧
    4 * r ≤ Y := by
  have hY0_ge : 2 ^ 100 ≤ dyadicY0 := by
    dsimp [dyadicY0]; exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
  have hY_ge100 : 2 ^ 100 ≤ Y := hY0_ge.trans hY_small
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := by
    have : 0 < Y := lt_of_lt_of_le (Nat.pow_pos two_pos) hY_ge100
    exact Nat.cast_pos.mpr this
  set Q := Nat.sqrt (Y / r)
  set Q₀ := Q / 2 ^ 24
  have hr_le_Y25 : (r : ℝ) ≤ (Y : ℝ) ^ ((2 : ℝ) / 5) := by
    have hR : ((r : ℝ) ^ (5 : ℕ)) ≤ (Y : ℝ) ^ (2 : ℕ) := by exact_mod_cast hr_big
    calc (r : ℝ) = ((r : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hr_pos.le]; norm_num
      _ ≤ ((Y : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 5) := Real.rpow_le_rpow (by positivity) hR (by norm_num)
      _ = (Y : ℝ) ^ ((2 : ℝ) / 5) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hY_pos.le]; norm_num
  have hY35_le : (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ (Y : ℝ) / (r : ℝ) := by
    rw [le_div_iff₀ hr_pos]
    calc (Y : ℝ) ^ ((3 : ℝ) / 5) * (r : ℝ)
        ≤ (Y : ℝ) ^ ((3 : ℝ) / 5) * (Y : ℝ) ^ ((2 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_left hr_le_Y25 (by positivity)
      _ = (Y : ℝ) := by rw [← Real.rpow_add hY_pos]; norm_num
  have hY35_ge : (2 : ℝ) ^ 60 ≤ (Y : ℝ) ^ ((3 : ℝ) / 5) := by
    have h100 : ((2 : ℝ) ^ 100) ≤ (Y : ℝ) := by exact_mod_cast hY_ge100
    have h60 : (2 : ℝ) ^ 60 = ((2 : ℝ) ^ 100) ^ ((3 : ℝ) / 5) := by
      rw [← Real.rpow_natCast (2 : ℝ) 60, ← Real.rpow_natCast (2 : ℝ) 100, ← Real.rpow_mul zero_le_two]
      congr 1; norm_num
    rw [h60]
    exact Real.rpow_le_rpow (by positivity) h100 (by norm_num)
  have hYr_ge59 : 2 ^ 59 ≤ Y / r := by
    have h1 : (2 : ℝ) ^ 60 ≤ (Y : ℝ) / (r : ℝ) := hY35_ge.trans hY35_le
    have h2 : (Y : ℝ) / (r : ℝ) ≤ ((Y / r + 1 : ℕ) : ℝ) := by
      have hd := Nat.div_add_mod Y r
      have hm := Nat.mod_lt Y hr
      have hmul : (Y / r + 1) * r = r * (Y / r) + r := by ring
      rw [div_le_iff₀ hr_pos]
      exact_mod_cast (by omega : Y ≤ (Y / r + 1) * r)
    have h3 : (2 : ℝ) ^ 59 + 1 ≤ (2 : ℝ) ^ 60 := by
      have h59 : (1 : ℝ) ≤ (2 : ℝ) ^ 59 := one_le_pow₀ (by norm_num)
      rw [pow_succ]; linarith only [h59]
    have h4 : (2 : ℝ) ^ 59 + 1 ≤ ((Y / r + 1 : ℕ) : ℝ) := by linarith only [h1, h2, h3]
    have h5 : ((2 ^ 59 + 1 : ℕ) : ℝ) ≤ ((Y / r + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h4
    have h6 : 2 ^ 59 + 1 ≤ Y / r + 1 := by exact_mod_cast h5
    exact Nat.le_of_add_le_add_right h6
  have hQ_ge25 : 2 ^ 25 ≤ Q := by
    dsimp [Q]
    rw [Nat.le_sqrt]
    have hpow : 2 ^ 25 * 2 ^ 25 ≤ 2 ^ 59 := by
      rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact hpow.trans hYr_ge59
  have hQ0_le_Y : Q₀ ≤ Y := by
    have h1 : Q₀ ≤ Q := Nat.div_le_self Q (2 ^ 24)
    have h2 : Q ≤ Y / r := Nat.sqrt_le_self (Y / r)
    have h3 : Y / r ≤ Y := Nat.div_le_self Y r
    exact h1.trans (h2.trans h3)
  have h4rY : 4 * r ≤ Y := by
    have h4_le : 4 ≤ Y / r :=
      le_trans (show 4 ≤ 2 ^ 59 from le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hYr_ge59
    calc 4 * r = r * 4 := mul_comm _ _
      _ ≤ r * (Y / r) := Nat.mul_le_mul_left r h4_le
      _ ≤ Y := Nat.mul_div_le Y r
  exact ⟨hY35_le, hQ_ge25, hQ0_le_Y, h4rY⟩

private lemma dyadic_main_regime_rankin {r Y : ℕ} (hr : 0 < r)
    (hY_small : dyadicY0 ≤ Y)
    (hY35_le : (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ (Y : ℝ) / (r : ℝ))
    (hQ_ge25 : 2 ^ 25 ≤ Nat.sqrt (Y / r)) :
    rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16) ≤
      (1 / 4 : ℝ) * Real.sqrt ((Nat.sqrt (Y / r) / 2 ^ 24 : ℕ) : ℝ) := by
  let A_rankin : ℝ := 8 * rankinConst * (2 : ℝ) ^ 13
  have hY0_ge : 2 ^ 100 ≤ dyadicY0 := by
    dsimp [dyadicY0]; exact le_trans (le_max_left _ _) (Nat.le_add_right _ _)
  have hY_ge100 : 2 ^ 100 ≤ Y := hY0_ge.trans hY_small
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (lt_of_lt_of_le (Nat.pow_pos two_pos) hY_ge100)
  set Q := Nat.sqrt (Y / r)
  set Q₀ := Q / 2 ^ 24
  have hQ_lo : (1 / 2 : ℝ) * (Y : ℝ) ^ ((3 : ℝ) / 10) ≤ (Q : ℝ) := by
    have hsucc : Y / r < (Q + 1) * (Q + 1) := Nat.lt_succ_sqrt (Y / r)
    have hdiv : (Y : ℝ) / (r : ℝ) ≤ ((Y / r + 1 : ℕ) : ℝ) := by
      have hd := Nat.div_add_mod Y r; have hm := Nat.mod_lt Y hr
      have hmul : (Y / r + 1) * r = r * (Y / r) + r := by ring
      rw [div_le_iff₀ hr_pos]; exact_mod_cast (by omega : Y ≤ (Y / r + 1) * r)
    have hQ1 : Q + 1 ≤ 2 * Q := by
      have hQ_pos : 1 ≤ Q := le_trans (Nat.one_le_pow 25 2 (by norm_num)) hQ_ge25
      omega
    have hsq : (Y : ℝ) ^ ((3 : ℝ) / 5) ≤ ((2 * Q : ℕ) : ℝ) ^ 2 := by
      have hnat : Y / r + 1 ≤ (2 * Q) ^ 2 := by
        calc Y / r + 1 ≤ (Q + 1) * (Q + 1) := hsucc
          _ ≤ (2 * Q) * (2 * Q) := Nat.mul_le_mul hQ1 hQ1
          _ = (2 * Q) ^ 2 := (sq _).symm
      exact hY35_le.trans (hdiv.trans (by exact_mod_cast hnat))
    have hrt := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_mul hY_pos.le] at hrt
    have h310 : (3 : ℝ) / 5 * ((1 : ℝ) / 2) = 3 / 10 := by norm_num
    rw [h310] at hrt
    push_cast at hrt
    linarith only [hrt]
  have hQ0_lo : (1 / (2 : ℝ) ^ 26) * (Y : ℝ) ^ ((3 : ℝ) / 10) ≤ (Q₀ : ℝ) := by
    have h1 : Q ≤ 2 ^ 24 * (Q₀ + 1) := by
      have hdm := Nat.div_add_mod Q (2 ^ 24)
      have hml := Nat.mod_lt Q (by positivity : 0 < 2 ^ 24)
      dsimp [Q₀]
      have heq : 2 ^ 24 * (Q / 2 ^ 24 + 1) = 2 ^ 24 * (Q / 2 ^ 24) + 2 ^ 24 := by ring
      omega
    have h2 : 1 ≤ Q₀ := by
      dsimp [Q₀]
      have hdiv : 1 * 2 ^ 24 ≤ Q := by
        rw [one_mul]
        exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hQ_ge25
      exact (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ 24)).2 hdiv
    have h3 : Q ≤ 2 ^ 25 * Q₀ := by
      have hmul : 2 ^ 24 * (Q₀ + 1) ≤ 2 ^ 24 * (2 * Q₀) := Nat.mul_le_mul_left _ (by omega)
      have heq : 2 ^ 24 * (2 * Q₀) = 2 ^ 25 * Q₀ := by rw [← mul_assoc, ← pow_succ]
      exact h1.trans (hmul.trans heq.le)
    have h3R : (Q : ℝ) ≤ (2 : ℝ) ^ 25 * (Q₀ : ℝ) := by exact_mod_cast h3
    have hpow26 : (1 / (2 : ℝ) ^ 26) * (Y : ℝ) ^ ((3 : ℝ) / 10) =
        (1 / (2 : ℝ) ^ 25) * ((1 / 2 : ℝ) * (Y : ℝ) ^ ((3 : ℝ) / 10)) := by
      rw [pow_succ]; ring
    have hdiv := mul_le_mul_of_nonneg_left (hQ_lo.trans h3R) (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ 25)
    have hcancel : (1 / (2 : ℝ) ^ 25) * ((2 : ℝ) ^ 25 * (Q₀ : ℝ)) = (Q₀ : ℝ) := by
      have hne : (2 : ℝ) ^ 25 ≠ 0 := by positivity
      field_simp [hne]
    linarith only [hpow26, hdiv, hcancel]
  have hsqrtQ0 : (1 / (2 : ℝ) ^ 13) * (Y : ℝ) ^ ((3 : ℝ) / 20) ≤ Real.sqrt (Q₀ : ℝ) := by
    have hrt := Real.sqrt_le_sqrt hQ0_lo
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow ((Y : ℝ) ^ ((3 : ℝ) / 10)),
        ← Real.rpow_mul hY_pos.le] at hrt
    have h13 : Real.sqrt (1 / (2 : ℝ) ^ 26) = 1 / (2 : ℝ) ^ 13 := by
      have : (1 / (2 : ℝ) ^ 26) = (1 / (2 : ℝ) ^ 13) ^ 2 := by
        rw [one_div_pow, ← pow_mul]
      rw [this, Real.sqrt_sq (by positivity)]
    have h320 : (3 : ℝ) / 10 * ((1 : ℝ) / 2) = 3 / 20 := by norm_num
    rw [h13, h320] at hrt
    exact hrt
  have hA_le : A_rankin ≤ (Y : ℝ) ^ ((7 : ℝ) / 80) := by
    have hA_pos : 0 < A_rankin := by
      dsimp [A_rankin]
      exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 8) rankinConst_pos) (pow_pos two_pos 13)
    have hceil : A_rankin ^ ((80 : ℝ) / 7) ≤ (Y : ℝ) := by
      have h1 : Nat.ceil (A_rankin ^ ((80 : ℝ) / 7)) ≤ Y := by
        have : Nat.ceil (A_rankin ^ ((80 : ℝ) / 7)) ≤ dyadicY0 := by
          dsimp [dyadicY0, A_rankin]; exact le_trans (le_max_right _ _) (Nat.le_add_right _ _)
        exact this.trans hY_small
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr h1)
    calc A_rankin = (A_rankin ^ ((80 : ℝ) / 7)) ^ ((7 : ℝ) / 80) := by
          rw [← Real.rpow_mul hA_pos.le]; norm_num
      _ ≤ (Y : ℝ) ^ ((7 : ℝ) / 80) := Real.rpow_le_rpow (Real.rpow_nonneg hA_pos.le _) hceil (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hA_le (by positivity : 0 ≤ (Y : ℝ) ^ ((1 : ℝ) / 16))
  rw [← Real.rpow_add hY_pos] at hmul
  have h320' : (7 : ℝ) / 80 + 1 / 16 = 3 / 20 := by norm_num
  rw [h320'] at hmul
  dsimp [A_rankin] at hmul
  have h1 : 4 * (2 : ℝ) ^ 13 * (rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16)) ≤ (Y : ℝ) ^ ((3 : ℝ) / 20) := by
    have hnn : 0 ≤ rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16) := mul_nonneg rankinConst_pos.le (by positivity)
    have heq : 8 * rankinConst * (2 : ℝ) ^ 13 * (Y : ℝ) ^ ((1 : ℝ) / 16) =
        2 * (4 * (2 : ℝ) ^ 13 * (rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16))) := by ring
    linarith only [hmul, hnn, heq]
  have h3 : rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16) ≤ (1 / 4 : ℝ) * (1 / (2 : ℝ) ^ 13 * (Y : ℝ) ^ ((3 : ℝ) / 20)) := by
    have hpos13 : (0 : ℝ) < (2 : ℝ) ^ 13 := pow_pos two_pos 13
    have hdiv := mul_le_mul_of_nonneg_left h1 (div_nonneg zero_le_one (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hpos13.le))
    have hL : (1 : ℝ) / (4 * (2 : ℝ) ^ 13) * (4 * (2 : ℝ) ^ 13 * (rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16))) =
        rankinConst * (Y : ℝ) ^ ((1 : ℝ) / 16) := by field_simp [hpos13.ne']
    have hR : (1 : ℝ) / (4 * (2 : ℝ) ^ 13) * (Y : ℝ) ^ ((3 : ℝ) / 20) =
        (1 / 4 : ℝ) * (1 / (2 : ℝ) ^ 13 * (Y : ℝ) ^ ((3 : ℝ) / 20)) := by ring
    linarith only [hdiv, hL, hR]
  exact h3.trans (mul_le_mul_of_nonneg_left hsqrtQ0 (by norm_num))

private lemma dyadicBound_main_regime {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
      ‖smoothedTiltedRemainder χ Y t‖ ≤
        C * Real.sqrt ((Y : ℝ) * (1 + |t| * (Y : ℝ))) * Real.log (2 * (d : ℝ) * (Y : ℝ)))
    {P : Progressions} {Y : ℕ} (hrY : P.r ≤ Y)
    (hY_small : dyadicY0 ≤ Y) (hr_big : P.r ^ 5 ≤ Y ^ 2) :
    ((dyadicExceptions P Y).card : ℝ) ≤
      (2 * (262144 : ℝ) ^ 2 * (6 * C + ((2 : ℝ) ^ 144) ^ 2) ^ 2 * (37 + 22 * C)) *
        dyadicBudget Y P.r := by
  let C_rem : ℝ := 6 * C + ((2 : ℝ) ^ 144) ^ 2
  let C_main : ℝ := 2 * (262144 : ℝ) ^ 2 * C_rem ^ 2 * (37 + 22 * C)
  set r := P.r
  set Q := Nat.sqrt (Y / r)
  set Q₀ := Q / 2 ^ 24
  set H := Y / r + 1
  have hr : 0 < r := P.r_pos
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hY0_ge : 2 ^ 100 ≤ dyadicY0 := by dsimp [dyadicY0]; omega
  have hY_ge100 : 2 ^ 100 ≤ Y := hY0_ge.trans hY_small
  have hY_ge72 : 2 ^ 72 ≤ Y := le_trans (by norm_num : 2 ^ 72 ≤ 2 ^ 100) hY_ge100
  have hY_ge2 : 2 ≤ Y := le_trans (by norm_num : 2 ≤ 2 ^ 100) hY_ge100
  have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hlog1 : (1 : ℝ) ≤ Real.log (2 * (Y : ℝ)) := one_le_log_two_mul hY_ge2
  obtain ⟨hY35_le, hQ_ge25, hQ0_le_Y, h4rY⟩ := dyadic_main_regime_basic hr hY_small hr_big
  have hRankin_Y := dyadic_main_regime_rankin hr hY_small hY35_le hQ_ge25
  let badK : Finset ℕ := (dyadicExceptions P Y).image (fun n => (n - (P.b₁ + P.b₂)) / r)
  have hcard_eq : (dyadicExceptions P Y).card = badK.card := by
    symm
    refine Finset.card_image_of_injOn fun n₁ h1 n₂ h2 hEq => ?_
    have hrec : ∀ n ∈ dyadicExceptions P Y, r * ((n - (P.b₁ + P.b₂)) / r) + P.b₁ + P.b₂ = n := by
      intro n hn
      have hlo : Y / 2 < n := (Finset.mem_filter.mp hn).2
      have hmod : n % r = (P.b₁ + P.b₂) % r := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2.2.1
      have hge_b : P.b₁ + P.b₂ ≤ n := by have := P.b₁_lt; have := P.b₂_lt; omega
      have hdvd : r ∣ n - (P.b₁ + P.b₂) := by
        have hm : n ≡ P.b₁ + P.b₂ [MOD r] := hmod
        exact (Nat.modEq_iff_dvd' hge_b).1 hm.symm
      have hmul := Nat.mul_div_cancel' hdvd
      omega
    rw [← hrec n₁ h1, ← hrec n₂ h2, hEq]
  have hbadK_sub : badK ⊆ Finset.range H := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hnY : n ≤ Y := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1).2
    have hle : (n - (P.b₁ + P.b₂)) / r ≤ Y / r := Nat.div_le_div_right ((Nat.sub_le n (P.b₁ + P.b₂)).trans hnY)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  let S₁ := smoothedPrimeSum r P.b₁ Y
  let S₂ := smoothedPrimeSum r P.b₂ Y
  let M₁ := modelSum r P.b₁ Y Q Q₀
  let M₂ := modelSum r P.b₂ Y Q Q₀
  let F : ℝ → ℂ := fun α => S₁ α * S₂ α - M₁ α * M₂ α
  let err : ℕ → ℂ := fun k => ∫ α in (0 : ℝ)..1, F α * e (-((k : ℝ) * α))
  let thresh : ℝ := ((1 : ℝ) / 262144) * ((r : ℝ) / (r.totient : ℝ)) ^ 2 * ((Y : ℝ) / (r : ℝ))
  have hbad_thresh : ∀ k ∈ badK, thresh ≤ ‖err k‖ := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hlo : Y / 2 < n := (Finset.mem_filter.mp hn).2
    have hmem_exc := Finset.mem_filter.mp (Finset.mem_filter.mp hn).1
    have hn_hi : n ≤ Y := (Finset.mem_Icc.mp hmem_exc.1).2
    have hn_even : Even n := hmem_exc.2.1
    have hmod : n % r = (P.b₁ + P.b₂) % r := hmem_exc.2.2.1
    have hexc0 : (primeRepresentations P n).card = 0 := hmem_exc.2.2.2
    have hge_b : P.b₁ + P.b₂ ≤ n := by have := P.b₁_lt; have := P.b₂_lt; omega
    have hdvd : r ∣ n - (P.b₁ + P.b₂) := (Nat.modEq_iff_dvd' hge_b).1 hmod.symm
    set k' := (n - (P.b₁ + P.b₂)) / r
    have hnk : r * k' + P.b₁ + P.b₂ = n := by
      have hmul : r * k' = n - (P.b₁ + P.b₂) := Nat.mul_div_cancel' hdvd
      omega
    have hk'_le : k' ≤ Y / r := Nat.div_le_div_right ((Nat.sub_le n (P.b₁ + P.b₂)).trans hn_hi)
    have hS_int : IntervalIntegrable (fun α => S₁ α * S₂ α * e (-((k' : ℝ) * α))) MeasureTheory.volume 0 1 := by
      have hcont : Continuous (fun α => S₁ α * S₂ α * e (-((k' : ℝ) * α))) := by
        refine ((continuous_smoothedPrimeSum r P.b₁ Y).mul (continuous_smoothedPrimeSum r P.b₂ Y)).mul ?_
        have h : (fun α : ℝ => e (-((k' : ℝ) * α))) = fun α : ℝ => e (-(k' : ℝ) * α) := by funext α; ring_nf
        rw [h]; exact continuous_e_mul (-(k' : ℝ))
      exact hcont.intervalIntegrable 0 1
    have hM_int : IntervalIntegrable (fun α => M₁ α * M₂ α * e (-((k' : ℝ) * α))) MeasureTheory.volume 0 1 := by
      obtain ⟨B1, hB1⟩ := modelSum_norm_bounded r P.b₁ Y Q Q₀
      obtain ⟨B2, hB2⟩ := modelSum_norm_bounded r P.b₂ Y Q Q₀
      have hB1_nn : 0 ≤ B1 := (norm_nonneg (M₁ 0)).trans (hB1 0)
      have he_meas : Measurable (fun α : ℝ => e (-((k' : ℝ) * α))) := by
        have h : (fun α : ℝ => e (-((k' : ℝ) * α))) = fun α : ℝ => e (-(k' : ℝ) * α) := by funext α; ring_nf
        rw [h]; exact (continuous_e_mul (-(k' : ℝ))).measurable
      have hmeas : Measurable (fun α => M₁ α * M₂ α * e (-((k' : ℝ) * α))) :=
        ((modelSum_measurable r P.b₁ Y Q Q₀).mul (modelSum_measurable r P.b₂ Y Q Q₀)).mul he_meas
      refine intervalIntegrable_of_measurable_bounded (B := B1 * B2) hmeas fun α => ?_
      rw [norm_mul, norm_mul, norm_e, mul_one]
      exact mul_le_mul (hB1 α) (hB2 α) (norm_nonneg _) hB1_nn
    have herr_eq : err k' = -(∫ α in (0 : ℝ)..1, M₁ α * M₂ α * e (-((k' : ℝ) * α))) := by
      dsimp [err, F]
      have hfun : (fun α => (S₁ α * S₂ α - M₁ α * M₂ α) * e (-((k' : ℝ) * α))) =
          fun α => S₁ α * S₂ α * e (-((k' : ℝ) * α)) - M₁ α * M₂ α * e (-((k' : ℝ) * α)) := by
        funext α; ring
      rw [hfun, intervalIntegral.integral_sub hS_int hM_int,
          primeConvolution_eq_zero_of_exception P hk'_le (hnk.symm ▸ hexc0), zero_sub]
    rw [herr_eq, norm_neg]
    have hRankin_n : rankinConst * ((r * k' + P.b₁ + P.b₂ : ℕ) : ℝ) ^ ((1 : ℝ) / 16) ≤
        (1 / 4 : ℝ) * Real.sqrt ((Nat.sqrt (Y / r) / 2 ^ 24 : ℕ) : ℝ) := by
      rw [hnk]
      exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hn_hi) (by norm_num))
        rankinConst_pos.le).trans hRankin_Y
    have hconv_lo := modelSum_conv_re_lower hr P.b₁_lt P.b₂_lt (hnk.symm ▸ hlo) (hnk.symm ▸ hn_hi)
      (hnk.symm ▸ hn_even) hQ_ge25 hRankin_n
    exact hconv_lo.trans (Complex.re_le_norm _)
  have hF_meas : Measurable F :=
    ((continuous_smoothedPrimeSum r P.b₁ Y).measurable.mul (continuous_smoothedPrimeSum r P.b₂ Y).measurable).sub
      ((modelSum_measurable r P.b₁ Y Q Q₀).mul (modelSum_measurable r P.b₂ Y Q Q₀))
  have hF_bound : ∃ BF : ℝ, ∀ α, ‖F α‖ ≤ BF := by
    obtain ⟨B1, hB1⟩ := modelSum_norm_bounded r P.b₁ Y Q Q₀
    obtain ⟨B2, hB2⟩ := modelSum_norm_bounded r P.b₂ Y Q Q₀
    have hS_bound : ∀ b, ∃ BS : ℝ, ∀ α, ‖smoothedPrimeSum r b Y α‖ ≤ BS := fun b =>
      ⟨∑ j ∈ Finset.range (Y / r + 1), |quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)|,
        fun α => by
          unfold smoothedPrimeSum
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]⟩
    obtain ⟨BS1, hBS1⟩ := hS_bound P.b₁
    obtain ⟨BS2, hBS2⟩ := hS_bound P.b₂
    refine ⟨BS1 * BS2 + B1 * B2, fun α => ?_⟩
    have hBS1_nn : 0 ≤ BS1 := (norm_nonneg (S₁ 0)).trans (hBS1 0)
    have hB1_nn : 0 ≤ B1 := (norm_nonneg (M₁ 0)).trans (hB1 0)
    calc ‖S₁ α * S₂ α - M₁ α * M₂ α‖ ≤ ‖S₁ α * S₂ α‖ + ‖M₁ α * M₂ α‖ := norm_sub_le _ _
      _ = ‖S₁ α‖ * ‖S₂ α‖ + ‖M₁ α‖ * ‖M₂ α‖ := by rw [norm_mul, norm_mul]
      _ ≤ BS1 * BS2 + B1 * B2 := add_le_add
          (mul_le_mul (hBS1 α) (hBS2 α) (norm_nonneg _) hBS1_nn)
          (mul_le_mul (hB1 α) (hB2 α) (norm_nonneg _) hB1_nn)
  obtain ⟨BF, hBF⟩ := hF_bound
  have hcard_bessel : (badK.card : ℝ) * thresh ^ 2 ≤ ∫ α in (0 : ℝ)..1, ‖F α‖ ^ 2 :=
    (card_mul_sq_le_sum hbadK_sub err (by positivity) hbad_thresh).trans
      (bessel_intervalIntegral hF_meas hBF H)
  set R_sup : ℝ := C_rem * (Y : ℝ) ^ ((3 : ℝ) / 4) * (r : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (2 * (Y : ℝ))
  have hF2_pt : ∀ α : ℝ, ‖F α‖ ^ 2 ≤ 2 * R_sup ^ 2 * (‖S₂ α‖ ^ 2 + ‖M₁ α‖ ^ 2) := by
    intro α
    have hdecomp : F α = (S₁ α - M₁ α) * S₂ α + M₁ α * (S₂ α - M₂ α) := by dsimp [F]; ring
    have hR1 := remainder_sup_le hC hTw hr hrY P.b₁_lt P.coprime₁ hQ_ge25 α
    have hR2 := remainder_sup_le hC hTw hr hrY P.b₂_lt P.coprime₂ hQ_ge25 α
    have hnorm : ‖F α‖ ≤ R_sup * (‖S₂ α‖ + ‖M₁ α‖) := by
      rw [hdecomp]
      calc ‖(S₁ α - M₁ α) * S₂ α + M₁ α * (S₂ α - M₂ α)‖
          ≤ ‖(S₁ α - M₁ α) * S₂ α‖ + ‖M₁ α * (S₂ α - M₂ α)‖ := norm_add_le _ _
        _ = ‖S₁ α - M₁ α‖ * ‖S₂ α‖ + ‖M₁ α‖ * ‖S₂ α - M₂ α‖ := by rw [norm_mul, norm_mul]
        _ ≤ R_sup * ‖S₂ α‖ + ‖M₁ α‖ * R_sup := add_le_add
            (mul_le_mul_of_nonneg_right hR1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_left hR2 (norm_nonneg _))
        _ = R_sup * (‖S₂ α‖ + ‖M₁ α‖) := by ring
    have hsq : ‖F α‖ ^ 2 ≤ (R_sup * (‖S₂ α‖ + ‖M₁ α‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h2ab : (‖S₂ α‖ + ‖M₁ α‖) ^ 2 ≤ 2 * (‖S₂ α‖ ^ 2 + ‖M₁ α‖ ^ 2) := by
      nlinarith only [sq_nonneg (‖S₂ α‖ - ‖M₁ α‖)]
    calc ‖F α‖ ^ 2 ≤ R_sup ^ 2 * (‖S₂ α‖ + ‖M₁ α‖) ^ 2 := by rw [← mul_pow]; exact hsq
      _ ≤ R_sup ^ 2 * (2 * (‖S₂ α‖ ^ 2 + ‖M₁ α‖ ^ 2)) := mul_le_mul_of_nonneg_left h2ab (sq_nonneg _)
      _ = 2 * R_sup ^ 2 * (‖S₂ α‖ ^ 2 + ‖M₁ α‖ ^ 2) := by ring
  have hF2_int : IntervalIntegrable (fun α => ‖F α‖ ^ 2) MeasureTheory.volume 0 1 := by
    have hBF_nn : 0 ≤ BF := (norm_nonneg (F 0)).trans (hBF 0)
    refine intervalIntegrable_of_measurable_bounded (B := BF ^ 2)
      ((continuous_norm.measurable.comp hF_meas).pow_const 2) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hBF α) 2
  have hS2_int : IntervalIntegrable (fun α => ‖S₂ α‖ ^ 2) MeasureTheory.volume 0 1 :=
    ((continuous_norm.comp (continuous_smoothedPrimeSum r P.b₂ Y)).pow 2).intervalIntegrable 0 1
  have hM1_int : IntervalIntegrable (fun α => ‖M₁ α‖ ^ 2) MeasureTheory.volume 0 1 := by
    obtain ⟨B1, hB1⟩ := modelSum_norm_bounded r P.b₁ Y Q Q₀
    refine intervalIntegrable_of_measurable_bounded (B := B1 ^ 2)
      ((continuous_norm.measurable.comp (modelSum_measurable r P.b₁ Y Q Q₀)).pow_const 2) fun α => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB1 α) 2
  have hL2_F : (∫ α in (0 : ℝ)..1, ‖F α‖ ^ 2) ≤
      2 * R_sup ^ 2 * ((37 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) *
        Real.log (2 * (Y : ℝ))) := by
    have hmono := intervalIntegral.integral_mono_on zero_le_one hF2_int
      ((hS2_int.add hM1_int).const_mul (2 * R_sup ^ 2)) (fun α _ => hF2_pt α)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hS2_int hM1_int] at hmono
    have hS2_le := smoothedPrimeSum_l2_le hC hTw hr hrY hY_ge2 P.b₂_lt P.coprime₂
    have hM1_le : (∫ α in (0 : ℝ)..1, ‖M₁ α‖ ^ 2) ≤
        36 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) :=
      modelSum_l2_le (b := P.b₁) (Q := Q) (Q₀ := Q₀) hr hrY hQ0_le_Y hY_ge72
    have hrtot_ge1 : (1 : ℝ) ≤ (r : ℝ) / (r.totient : ℝ) := by
      rw [one_le_div (Nat.cast_pos.mpr (Nat.totient_pos.mpr hr))]
      exact Nat.cast_le.mpr (Nat.totient_le r)
    have hsqrt_log : Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) ≤ 11 * ((Y : ℝ) / (r : ℝ)) := by
      have hl := log_two_mul_le_rpow_tenth (by omega : 1 ≤ Y)
      calc Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))
          ≤ (Y : ℝ) ^ ((1 : ℝ) / 2) * (11 * (Y : ℝ) ^ ((1 : ℝ) / 10)) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_left hl (by positivity)
        _ = 11 * ((Y : ℝ) ^ ((1 : ℝ) / 2) * (Y : ℝ) ^ ((1 : ℝ) / 10)) := by ring
        _ = 11 * (Y : ℝ) ^ ((3 : ℝ) / 5) := by rw [← Real.rpow_add hY_pos]; norm_num
        _ ≤ 11 * ((Y : ℝ) / (r : ℝ)) := mul_le_mul_of_nonneg_left hY35_le (by norm_num)
    have hS2_clean : (∫ α in (0 : ℝ)..1, ‖S₂ α‖ ^ 2) ≤
        (1 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
      have hterm : 2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) ≤
          22 * C * (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ))) := by
        calc 2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))
            = 2 * C * (Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) := by ring
          _ ≤ 2 * C * (11 * ((Y : ℝ) / (r : ℝ))) := mul_le_mul_of_nonneg_left hsqrt_log (by positivity)
          _ = 22 * C * ((Y : ℝ) / (r : ℝ)) := by ring
          _ ≤ 22 * C * (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ))) :=
              mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hrtot_ge1) (by positivity)
      have hsum_in : ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) +
          2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) ≤
          (1 + 22 * C) * (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ))) := by linarith
      calc (∫ α in (0 : ℝ)..1, ‖S₂ α‖ ^ 2)
          ≤ (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) +
              2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) * Real.log (2 * (Y : ℝ)) := hS2_le
        _ ≤ ((1 + 22 * C) * (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)))) * Real.log (2 * (Y : ℝ)) :=
            mul_le_mul_of_nonneg_right hsum_in (by linarith)
        _ = (1 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by ring
    have hsum_L2 : (∫ α in (0 : ℝ)..1, ‖S₂ α‖ ^ 2) + (∫ α in (0 : ℝ)..1, ‖M₁ α‖ ^ 2) ≤
        (37 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
      calc (∫ α in (0 : ℝ)..1, ‖S₂ α‖ ^ 2) + (∫ α in (0 : ℝ)..1, ‖M₁ α‖ ^ 2)
          ≤ (1 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) +
            36 * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) :=
              add_le_add hS2_clean hM1_le
        _ = (37 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by ring
    exact hmono.trans (mul_le_mul_of_nonneg_left hsum_L2 (by positivity))
  have hthresh_pos : 0 < thresh := by
    dsimp [thresh]
    have : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
    positivity
  have hdiv := (le_div_iff₀ (pow_pos hthresh_pos 2)).2 (hcard_bessel.trans hL2_F)
  have halg : (2 * R_sup ^ 2 * ((37 + 22 * C) * ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) *
      Real.log (2 * (Y : ℝ)))) / thresh ^ 2 = C_main * dyadicBudget Y r := by
    unfold dyadicBudget
    dsimp [R_sup, thresh, C_main]
    have hrt_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
    have hY34_sq : ((Y : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = (Y : ℝ) * Real.sqrt (Y : ℝ) := by
      rw [← Real.rpow_natCast ((Y : ℝ) ^ ((3 : ℝ) / 4)) 2, ← Real.rpow_mul hY_pos.le,
          Real.sqrt_eq_rpow, ← Real.rpow_one_add' hY_pos.le (by norm_num)]
      norm_num
    have hr14_sq : ((r : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = 1 / Real.sqrt (r : ℝ) := by
      rw [← Real.rpow_natCast ((r : ℝ) ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul hr_pos.le,
          Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hr_pos.le]
      norm_num
    have hsqrt_mul : Real.sqrt ((Y : ℝ) * (r : ℝ)) = Real.sqrt (Y : ℝ) * Real.sqrt (r : ℝ) :=
      Real.sqrt_mul hY_pos.le _
    have hsq_r_ne : Real.sqrt (r : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hr_pos).ne'
    have hR2 : (C_rem * (Y : ℝ) ^ ((3 : ℝ) / 4) * (r : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (2 * (Y : ℝ))) ^ 2 =
        C_rem ^ 2 * ((Y : ℝ) * Real.sqrt (Y : ℝ)) * (1 / Real.sqrt (r : ℝ)) * (Real.log (2 * (Y : ℝ))) ^ 2 := by
      calc (C_rem * (Y : ℝ) ^ ((3 : ℝ) / 4) * (r : ℝ) ^ (-(1 : ℝ) / 4) * Real.log (2 * (Y : ℝ))) ^ 2
          = C_rem ^ 2 * ((Y : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 * ((r : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 *
              (Real.log (2 * (Y : ℝ))) ^ 2 := by ring
        _ = _ := by rw [hY34_sq, hr14_sq]
    rw [hR2, hsqrt_mul]
    field_simp [hr_pos.ne', hrt_pos.ne', hY_pos.ne', hsq_r_ne]
    ring_nf
    rw [Real.sq_sqrt hr_pos.le]
  rw [hcard_eq]
  exact hdiv.trans halg.le

/-- **Module D2 (`SmoothedTwistEstimate → DyadicBound`):**
Proves the dyadic exception bound `(φ(r)/r)³ √(Yr) log³(2Y)` uniformly for all `Progressions`
and all `Y ≥ P.r`. -/
theorem dyadicBound_of_smoothedTwistEstimate : SmoothedTwistEstimate → DyadicBound := by
  rintro ⟨C, hC, hTw⟩
  -- Define an explicit threshold `Y₀` ensuring `2^72 ≤ Y`, `2^25 ≤ Q`, and `rankinConst * Y^(1/16) ≤ (1/4) * √Q₀`.
  let Y₀ : ℕ := dyadicY0
  have hY0_ge : 2 ^ 100 ≤ Y₀ := by dsimp [Y₀, dyadicY0]; omega
  -- Constants for each of the three regimes.
  let C_rem : ℝ := 6 * C + ((2 : ℝ) ^ 144) ^ 2
  let C_main : ℝ := 2 * (262144 : ℝ) ^ 2 * C_rem ^ 2 * (37 + 22 * C)
  let C_triv : ℝ := (2 : ℝ) ^ 49
  let C_small : ℝ := 8 * (Y₀ : ℝ) ^ 4
  refine ⟨max C_main (max C_triv C_small) + 1, by positivity, fun P Y hrY => ?_⟩
  set C_all := max C_main (max C_triv C_small) + 1
  have hC_main : C_main ≤ C_all := le_trans (le_max_left _ _) (by linarith)
  have hC_triv : C_triv ≤ C_all := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (by linarith)
  have hC_small : C_small ≤ C_all := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (by linarith)
  have hr : 0 < P.r := P.r_pos
  have hr_pos : (0 : ℝ) < P.r := Nat.cast_pos.mpr hr
  have hY_pos_nat : 0 < Y := lt_of_lt_of_le hr hrY
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr hY_pos_nat
  have hbud_nn : 0 ≤ dyadicBudget Y P.r := by
    unfold dyadicBudget
    have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr hY_pos_nat; linarith)
    positivity
  -- Split into three regimes: (1) `Y < Y₀`, (2) `Y ≥ Y₀ ∧ Y^2 < P.r^5`, (3) `Y ≥ Y₀ ∧ P.r^5 ≤ Y^2`.
  by_cases hY_small : Y < Y₀
  · -- Regime 1: Small `Y < Y₀`.
    have hcard_le : ((dyadicExceptions P Y).card : ℝ) ≤ (Y₀ : ℝ) := by
      have hsub : dyadicExceptions P Y ⊆ Finset.Icc 1 Y :=
        (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      have h1 : (dyadicExceptions P Y).card ≤ Y := (Finset.card_le_card hsub).trans (by simp)
      exact_mod_cast h1.trans hY_small.le
    have hbud_ge : 1 / (8 * (Y₀ : ℝ) ^ 3) ≤ dyadicBudget Y P.r := by
      unfold dyadicBudget
      have htot_ge : (1 : ℝ) / (Y₀ : ℝ) ≤ (P.r.totient : ℝ) / (P.r : ℝ) := by
        have h1 : (1 : ℝ) ≤ P.r.totient := Nat.one_le_cast.mpr (Nat.totient_pos.mpr hr)
        have h2 : (P.r : ℝ) ≤ Y₀ := Nat.cast_le.mpr (hrY.trans hY_small.le)
        calc (1 : ℝ) / (Y₀ : ℝ) ≤ 1 / (P.r : ℝ) := one_div_le_one_div_of_le hr_pos h2
          _ ≤ (P.r.totient : ℝ) / (P.r : ℝ) := div_le_div_of_nonneg_right h1 hr_pos.le
      have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt ((Y : ℝ) * (P.r : ℝ)) := by
        rw [Real.le_sqrt zero_le_one (by positivity)]
        have h1 : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr hY_pos_nat
        have h2 : (1 : ℝ) ≤ P.r := Nat.one_le_cast.mpr hr
        nlinarith only [h1, h2]
      have hlog_ge : (1 : ℝ) / 2 ≤ Real.log (2 * (Y : ℝ)) := by
        have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
          have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
            have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
              rw [← Real.exp_nat_mul]
              have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
              rw [this]; linarith [Real.exp_one_lt_d9]
            have hpos := Real.exp_pos (1 / 2 : ℝ)
            nlinarith only [hsq, hpos]
          have := Real.log_le_log (Real.exp_pos (1 / 2)) hexp
          rwa [Real.log_exp] at this
        have hle : Real.log 2 ≤ Real.log (2 * (Y : ℝ)) :=
          Real.log_le_log two_pos (by have : (1 : ℝ) ≤ Y := Nat.one_le_cast.mpr hY_pos_nat; linarith)
        linarith only [hlog2, hle]
      have hY0_pos : (0 : ℝ) < Y₀ := by exact_mod_cast (by omega : 0 < Y₀)
      have hpow1 : (1 / (Y₀ : ℝ)) ^ 3 ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) htot_ge 3
      have hpow2 : ((1 : ℝ) / 2) ^ 3 ≤ (Real.log (2 * (Y : ℝ))) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hlog_ge 3
      calc 1 / (8 * (Y₀ : ℝ) ^ 3) = (1 / (Y₀ : ℝ)) ^ 3 * 1 * ((1 : ℝ) / 2) ^ 3 := by ring
        _ ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ)) *
            (Real.log (2 * (Y : ℝ))) ^ 3 :=
          mul_le_mul (mul_le_mul hpow1 hsqrt_ge zero_le_one (by positivity)) hpow2 (by positivity) (by positivity)
    have hY0_pos : (0 : ℝ) < Y₀ := by exact_mod_cast (by omega : 0 < Y₀)
    have hstep : (Y₀ : ℝ) ≤ C_small * dyadicBudget Y P.r := by
      dsimp [C_small]
      have h1 := mul_le_mul_of_nonneg_left hbud_ge (by positivity : 0 ≤ 8 * (Y₀ : ℝ) ^ 4)
      have heq : 8 * (Y₀ : ℝ) ^ 4 * (1 / (8 * (Y₀ : ℝ) ^ 3)) = (Y₀ : ℝ) := by
        field_simp [hY0_pos.ne']
      linarith only [h1, heq]
    exact hcard_le.trans (hstep.trans (mul_le_mul_of_nonneg_right hC_small hbud_nn))
  · push Not at hY_small
    have hY_ge100 : 2 ^ 100 ≤ Y := hY0_ge.trans hY_small
    have hY_ge2 : 2 ≤ Y := le_trans (by norm_num : 2 ≤ 2 ^ 100) hY_ge100
    have hlog1 : (1 : ℝ) ≤ Real.log (2 * (Y : ℝ)) := one_le_log_two_mul hY_ge2
    by_cases hr_big : Y ^ 2 < P.r ^ 5
    · -- Regime 2: Large modulus `Y^2 < P.r^5`, use trivial congruence bound `2 * (Y / r)`.
      have hcard_le : ((dyadicExceptions P Y).card : ℝ) ≤ 2 * ((Y : ℝ) / (P.r : ℝ)) := by
        have hsub : dyadicExceptions P Y ⊆ (Finset.Icc 1 Y).filter (fun n => n % P.r = (P.b₁ + P.b₂) % P.r) := by
          intro n hn
          have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1)
          exact Finset.mem_filter.mpr ⟨h1.1, h1.2.2.1⟩
        have h1 : (dyadicExceptions P Y).card ≤ Y / P.r + 1 :=
          (Finset.card_le_card hsub).trans (card_congruence_Icc_le Y P.r _ hr)
        have hdiv : ((Y / P.r : ℕ) : ℝ) ≤ (Y : ℝ) / (P.r : ℝ) := by
          rw [le_div_iff₀ hr_pos]
          exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y P.r)
        have hge1 : (1 : ℝ) ≤ (Y : ℝ) / (P.r : ℝ) := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrY)
        have hcast : ((dyadicExceptions P Y).card : ℝ) ≤ ((Y / P.r : ℕ) : ℝ) + 1 := by exact_mod_cast h1
        linarith
      -- Show `2 * (Y / r) ≤ 2^49 * (φ(r)/r)³ * √(Yr) * log³(2Y)`.
      have hrtot_pos : (0 : ℝ) < P.r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
      have htot16 := div_totient_le_rpow_sixteenth P.r hr
      have hY_r54 : (Y : ℝ) ^ ((1 : ℝ) / 2) ≤ (P.r : ℝ) ^ ((5 : ℝ) / 4) := by
        have hR : ((Y : ℝ) ^ (2 : ℕ)) ≤ (P.r : ℝ) ^ (5 : ℕ) := by exact_mod_cast hr_big.le
        calc (Y : ℝ) ^ ((1 : ℝ) / 2) = ((Y : ℝ) ^ (2 : ℕ)) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hY_pos.le]; norm_num
          _ ≤ ((P.r : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) hR (by norm_num)
          _ = (P.r : ℝ) ^ ((5 : ℝ) / 4) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hr_pos.le]; norm_num
      have hstep : 2 * ((Y : ℝ) / (P.r : ℝ)) ≤ C_triv * dyadicBudget Y P.r := by
        unfold dyadicBudget
        dsimp [C_triv]
        have hlog3 : (1 : ℝ) ≤ (Real.log (2 * (Y : ℝ))) ^ 3 := by
          calc (1 : ℝ) = 1 ^ 3 := by norm_num
            _ ≤ (Real.log (2 * (Y : ℝ))) ^ 3 := pow_le_pow_left₀ zero_le_one hlog1 3
        have htot3 : ((P.r : ℝ) / (P.r.totient : ℝ)) ^ 3 ≤ (2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16) := by
          calc ((P.r : ℝ) / (P.r.totient : ℝ)) ^ 3
              ≤ ((2 : ℝ) ^ 16 * (P.r : ℝ) ^ ((1 : ℝ) / 16)) ^ 3 := pow_le_pow_left₀ (by positivity) htot16 3
            _ = (2 : ℝ) ^ 48 * ((P.r : ℝ) ^ ((1 : ℝ) / 16)) ^ (3 : ℕ) := by ring
            _ = (2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16) := by
                rw [← Real.rpow_natCast ((P.r : ℝ) ^ ((1 : ℝ) / 16)) 3, ← Real.rpow_mul hr_pos.le]; norm_num
        have hcore : 2 * ((P.r : ℝ) / (P.r.totient : ℝ)) ^ 3 * (Y : ℝ) ^ ((1 : ℝ) / 2) ≤
            (2 : ℝ) ^ 49 * (P.r : ℝ) ^ ((3 : ℝ) / 2) := by
          have hr_exp : (P.r : ℝ) ^ ((23 : ℝ) / 16) ≤ (P.r : ℝ) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hr) (by norm_num)
          calc 2 * ((P.r : ℝ) / (P.r.totient : ℝ)) ^ 3 * (Y : ℝ) ^ ((1 : ℝ) / 2)
              ≤ 2 * ((2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16)) * (P.r : ℝ) ^ ((5 : ℝ) / 4) :=
                mul_le_mul (mul_le_mul_of_nonneg_left htot3 two_pos.le) hY_r54 (by positivity) (by positivity)
            _ = (2 : ℝ) ^ 49 * ((P.r : ℝ) ^ ((3 : ℝ) / 16) * (P.r : ℝ) ^ ((5 : ℝ) / 4)) := by ring
            _ = (2 : ℝ) ^ 49 * (P.r : ℝ) ^ ((23 : ℝ) / 16) := by rw [← Real.rpow_add hr_pos]; norm_num
            _ ≤ (2 : ℝ) ^ 49 * (P.r : ℝ) ^ ((3 : ℝ) / 2) := mul_le_mul_of_nonneg_left hr_exp (by positivity)
        have hmul_eq : (2 * ((Y : ℝ) / (P.r : ℝ))) =
            (2 * ((P.r : ℝ) / (P.r.totient : ℝ)) ^ 3 * (Y : ℝ) ^ ((1 : ℝ) / 2)) *
              (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ)) / (P.r : ℝ) ^ ((3 : ℝ) / 2)) := by
          rw [Real.sqrt_eq_rpow, Real.mul_rpow hY_pos.le hr_pos.le]
          have hY1 : ((Y : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = (Y : ℝ) := by
            rw [← Real.rpow_natCast ((Y : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul hY_pos.le]; norm_num
          have hr32 : (P.r : ℝ) ^ ((3 : ℝ) / 2) = (P.r : ℝ) * (P.r : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_one_add' hr_pos.le (by norm_num)]; norm_num
          rw [hr32]
          have hr12_ne : (P.r : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hr_pos _).ne'
          field_simp [hr_pos.ne', hrtot_pos.ne', hr12_ne]
          exact hY1.symm
        have h1 : 2 * ((Y : ℝ) / (P.r : ℝ)) ≤
            (2 : ℝ) ^ 49 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ))) := by
          rw [hmul_eq]
          have hfactor := mul_le_mul_of_nonneg_right hcore
            (by positivity : 0 ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ)) / (P.r : ℝ) ^ ((3 : ℝ) / 2))
          have hsimp : (2 : ℝ) ^ 49 * (P.r : ℝ) ^ ((3 : ℝ) / 2) *
              (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ)) / (P.r : ℝ) ^ ((3 : ℝ) / 2)) =
              (2 : ℝ) ^ 49 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ))) := by
            have hr32_ne : (P.r : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hr_pos _).ne'
            field_simp [hr32_ne]
          linarith
        calc 2 * ((Y : ℝ) / (P.r : ℝ))
            ≤ (2 : ℝ) ^ 49 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ))) := h1
          _ ≤ (2 : ℝ) ^ 49 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ))) *
              (Real.log (2 * (Y : ℝ))) ^ 3 := le_mul_of_one_le_right (by positivity) hlog3
          _ = (2 : ℝ) ^ 49 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((Y : ℝ) * (P.r : ℝ)) *
              (Real.log (2 * (Y : ℝ))) ^ 3) := by ring
      exact hcard_le.trans (hstep.trans (mul_le_mul_of_nonneg_right hC_triv hbud_nn))
    · -- Regime 3: Main Farey regime (`Y ≥ Y₀` and `P.r ^ 5 ≤ Y ^ 2`).
      push Not at hr_big
      exact (dyadicBound_main_regime hC hTw hrY hY_small hr_big).trans
        (mul_le_mul_of_nonneg_right hC_main hbud_nn)

end DyadicTheorem

section GlobalTarget

/-- **Module E (`DyadicBound → Target`):**
Sums the dyadic bound over `Y_j = X / 2^j ≥ P.r`, handles at most one exception `n ≤ P.r`,
and combines with the trivial congruence bound `2 * X / P.r`. -/
theorem target_of_dyadicBound : DyadicBound → Target := by
  rintro ⟨Cd, hCd, hDyad⟩
  let C_final : ℝ := max 2 ((2 : ℝ) ^ 48 + 4 * Cd)
  refine ⟨C_final, by positivity, fun P X hX hrX => ?_⟩
  have hr : 0 < P.r := P.r_pos
  have hr_pos : (0 : ℝ) < P.r := Nat.cast_pos.mpr hr
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ C_final)]
  refine le_min ?_ ?_
  · -- Part 1: Trivial congruence bound `≤ 2 * (X / P.r) ≤ C_final * (X / P.r)`.
    have hsub : exceptions P X ⊆ (Finset.Icc 1 X).filter (fun n => n % P.r = (P.b₁ + P.b₂) % P.r) := by
      intro n hn
      have h := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨h.1, h.2.2.1⟩
    have h1 : (exceptions P X).card ≤ X / P.r + 1 :=
      (Finset.card_le_card hsub).trans (card_congruence_Icc_le X P.r _ hr)
    have hdiv : ((X / P.r : ℕ) : ℝ) ≤ (X : ℝ) / (P.r : ℝ) := by
      rw [le_div_iff₀ hr_pos]
      exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X P.r)
    have hge1 : (1 : ℝ) ≤ (X : ℝ) / (P.r : ℝ) := (one_le_div hr_pos).2 (Nat.cast_le.mpr hrX)
    have h2 : ((exceptions P X).card : ℝ) ≤ 2 * ((X : ℝ) / (P.r : ℝ)) := by
      have : ((exceptions P X).card : ℝ) ≤ ((X / P.r : ℕ) : ℝ) + 1 := by exact_mod_cast h1
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · -- Part 2: Dyadic decomposition of `exceptions P X` into `{n ≤ P.r}` and `{P.r < n ≤ X}`.
    let E_lo := (exceptions P X).filter (fun n => n ≤ P.r)
    let E_hi := (exceptions P X).filter (fun n => ¬ (n ≤ P.r))
    have hcard_split : (exceptions P X).card = E_lo.card + E_hi.card := by
      have hunion : E_lo ∪ E_hi = exceptions P X := by
        ext n; simp only [E_lo, E_hi, Finset.mem_union, Finset.mem_filter]
        exact ⟨fun h => h.elim And.left And.left, fun h => by
          by_cases hle : n ≤ P.r
          · exact Or.inl ⟨h, hle⟩
          · exact Or.inr ⟨h, hle⟩⟩
      have hdisj : Disjoint E_lo E_hi := Finset.disjoint_left.mpr fun n h1 h2 =>
        (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    -- At most 1 element in `E_lo` (since `Icc 1 r` has at most one element in any residue class mod `r`).
    have hlo_le : E_lo.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro n₁ h1 n₂ h2
      have h1_exc := Finset.mem_filter.mp (Finset.mem_filter.mp h1).1
      have h2_exc := Finset.mem_filter.mp (Finset.mem_filter.mp h2).1
      have h1_lo : 1 ≤ n₁ := (Finset.mem_Icc.mp h1_exc.1).1
      have h1_hi : n₁ ≤ P.r := (Finset.mem_filter.mp h1).2
      have h2_lo : 1 ≤ n₂ := (Finset.mem_Icc.mp h2_exc.1).1
      have h2_hi : n₂ ≤ P.r := (Finset.mem_filter.mp h2).2
      have hmod : n₁ % P.r = n₂ % P.r := h1_exc.2.2.1.trans h2_exc.2.2.1.symm
      by_cases hn1 : n₁ = P.r
      · by_cases hn2 : n₂ = P.r
        · exact hn1.trans hn2.symm
        · exfalso
          rw [hn1, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod
          omega
      · by_cases hn2 : n₂ = P.r
        · exfalso
          rw [hn2, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hmod
          omega
        · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
          exact hmod
    -- Cover `E_hi` by dyadic blocks `dyadicExceptions P (X / 2 ^ j)` for `j ∈ J`.
    let J := (Finset.range (X + 1)).filter (fun j => P.r ≤ X / 2 ^ j)
    have hhi_sub : E_hi ⊆ J.biUnion (fun j => dyadicExceptions P (X / 2 ^ j)) := by
      intro n hn
      have hn_exc := (Finset.mem_filter.mp hn).1
      have hn_gt_r : P.r < n := not_le.mp (Finset.mem_filter.mp hn).2
      have hn_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn_exc).1
      -- Pick the largest `j ≤ X` with `n ≤ X / 2 ^ j`.
      let S_n := (Finset.range (X + 1)).filter (fun j => n ≤ X / 2 ^ j)
      have hSn_ne : S_n.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa using hn_Icc.2⟩⟩
      let j := S_n.max' hSn_ne
      have hj_mem : j ∈ S_n := Finset.max'_mem S_n hSn_ne
      have hj_le_X : j ≤ X := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj_mem).1)
      have hn_le_Yj : n ≤ X / 2 ^ j := (Finset.mem_filter.mp hj_mem).2
      have hj_lt_X : j < X := by
        by_contra hge
        have hjX : j = X := by omega
        rw [hjX] at hn_le_Yj
        have hlt : X < 2 ^ X := Nat.lt_two_pow_self
        have hdiv0 : X / 2 ^ X = 0 := Nat.div_eq_of_lt hlt
        omega
      have hn_gt_half : (X / 2 ^ j) / 2 < n := by
        by_contra hle
        push Not at hle
        have hnext : n ≤ X / 2 ^ (j + 1) := by
          rw [pow_succ, ← Nat.div_div_eq_div_mul]; exact hle
        have hnext_mem : j + 1 ∈ S_n :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hnext⟩
        have hmax := Finset.le_max' S_n (j + 1) hnext_mem
        omega
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩, ?_⟩
      unfold dyadicExceptions exceptions
      have hprops := (Finset.mem_filter.mp hn_exc).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn_Icc.1, hn_le_Yj⟩, hprops⟩, hn_gt_half⟩
    have hhi_card : (E_hi.card : ℝ) ≤ 4 * Cd * dyadicBudget X P.r := by
      have h1 : E_hi.card ≤ ∑ j ∈ J, (dyadicExceptions P (X / 2 ^ j)).card :=
        (Finset.card_le_card hhi_sub).trans Finset.card_biUnion_le
      have hterm : ∀ j ∈ J, ((dyadicExceptions P (X / 2 ^ j)).card : ℝ) ≤
          Cd * ((1 / Real.sqrt 2) ^ j * dyadicBudget X P.r) := by
        intro j hj
        have hrYj : P.r ≤ X / 2 ^ j := (Finset.mem_filter.mp hj).2
        have hdy := hDyad P (X / 2 ^ j) hrYj
        have hYj_le : ((X / 2 ^ j : ℕ) : ℝ) ≤ (X : ℝ) / (2 : ℝ) ^ j := by
          rw [le_div_iff₀ (by positivity)]
          exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le X (2 ^ j))
        have hYj_leX : ((X / 2 ^ j : ℕ) : ℝ) ≤ (X : ℝ) := Nat.cast_le.mpr (Nat.div_le_self X (2 ^ j))
        have hYj_pos : 0 < X / 2 ^ j := lt_of_lt_of_le hr hrYj
        have hsqrt_le : Real.sqrt (((X / 2 ^ j : ℕ) : ℝ) * (P.r : ℝ)) ≤
            (1 / Real.sqrt 2) ^ j * Real.sqrt ((X : ℝ) * (P.r : ℝ)) := by
          have hpow2 : ((1 / Real.sqrt 2) ^ j) ^ 2 = 1 / (2 : ℝ) ^ j := by
            rw [← pow_mul, mul_comm j 2, pow_mul, one_div_pow, Real.sq_sqrt zero_le_two, one_div_pow]
          have hmul : ((X / 2 ^ j : ℕ) : ℝ) * (P.r : ℝ) ≤
              ((1 / Real.sqrt 2) ^ j) ^ 2 * ((X : ℝ) * (P.r : ℝ)) := by
            rw [hpow2]
            calc ((X / 2 ^ j : ℕ) : ℝ) * (P.r : ℝ) ≤ ((X : ℝ) / (2 : ℝ) ^ j) * (P.r : ℝ) :=
                  mul_le_mul_of_nonneg_right hYj_le hr_pos.le
              _ = 1 / (2 : ℝ) ^ j * ((X : ℝ) * (P.r : ℝ)) := by ring
          calc Real.sqrt (((X / 2 ^ j : ℕ) : ℝ) * (P.r : ℝ))
              ≤ Real.sqrt (((1 / Real.sqrt 2) ^ j) ^ 2 * ((X : ℝ) * (P.r : ℝ))) := Real.sqrt_le_sqrt hmul
            _ = (1 / Real.sqrt 2) ^ j * Real.sqrt ((X : ℝ) * (P.r : ℝ)) := by
                rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        have hlog_j_nn : 0 ≤ Real.log (2 * ((X / 2 ^ j : ℕ) : ℝ)) := Real.log_nonneg (by
          have : (1 : ℝ) ≤ ((X / 2 ^ j : ℕ) : ℝ) := Nat.one_le_cast.mpr hYj_pos; linarith)
        have hlog_le : (Real.log (2 * ((X / 2 ^ j : ℕ) : ℝ))) ^ 3 ≤ (Real.log (2 * (X : ℝ))) ^ 3 :=
          pow_le_pow_left₀ hlog_j_nn
            (Real.log_le_log (by positivity) (by linarith)) 3
        have hbud_le : dyadicBudget (X / 2 ^ j) P.r ≤ (1 / Real.sqrt 2) ^ j * dyadicBudget X P.r := by
          unfold dyadicBudget
          calc ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt (((X / 2 ^ j : ℕ) : ℝ) * (P.r : ℝ)) *
                (Real.log (2 * ((X / 2 ^ j : ℕ) : ℝ))) ^ 3
              ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * ((1 / Real.sqrt 2) ^ j * Real.sqrt ((X : ℝ) * (P.r : ℝ))) *
                (Real.log (2 * (X : ℝ))) ^ 3 := by
                refine mul_le_mul
                  (mul_le_mul_of_nonneg_left hsqrt_le (by positivity)) hlog_le (pow_nonneg hlog_j_nn 3) (by positivity)
            _ = (1 / Real.sqrt 2) ^ j * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ)) *
                (Real.log (2 * (X : ℝ))) ^ 3) := by ring
        exact hdy.trans (mul_le_mul_of_nonneg_left hbud_le hCd.le)
      have hgeom : ∑ j ∈ J, (1 / Real.sqrt 2) ^ j ≤ 4 := by
        have hlt : (1 : ℝ) / Real.sqrt 2 < 3 / 4 := by
          rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr two_pos) (by norm_num)]
          have : (4 : ℝ) < 3 * Real.sqrt 2 := by
            have hsq : (4 : ℝ) ^ 2 < (3 * Real.sqrt 2) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt zero_le_two]; norm_num
            nlinarith [Real.sqrt_nonneg 2]
          linarith
        calc ∑ j ∈ J, (1 / Real.sqrt 2) ^ j
            ≤ ∑ j ∈ Finset.range (X + 1), (1 / Real.sqrt 2) ^ j :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
          _ = ((1 / Real.sqrt 2) ^ (X + 1) - 1) / (1 / Real.sqrt 2 - 1) :=
              geom_sum_eq (by linarith) (X + 1)
          _ = (1 - (1 / Real.sqrt 2) ^ (X + 1)) / (1 - 1 / Real.sqrt 2) := by
              have hneg : 1 / Real.sqrt 2 - 1 = -(1 - 1 / Real.sqrt 2) := by ring
              rw [hneg, div_neg, ← neg_div, neg_sub]
          _ ≤ 1 / (1 - 1 / Real.sqrt 2) :=
              div_le_div_of_nonneg_right (by linarith [pow_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2) (X + 1)]) (by linarith)
          _ ≤ 1 / (1 / 4) := one_div_le_one_div_of_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
      have hbud_nn : 0 ≤ dyadicBudget X P.r := by
        unfold dyadicBudget
        have hlog_nn : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by
          have : (3 : ℝ) ≤ X := Nat.cast_le.mpr hX; linarith)
        positivity
      calc (E_hi.card : ℝ)
          ≤ ∑ j ∈ J, ((dyadicExceptions P (X / 2 ^ j)).card : ℝ) := by exact_mod_cast h1
        _ ≤ ∑ j ∈ J, Cd * ((1 / Real.sqrt 2) ^ j * dyadicBudget X P.r) := Finset.sum_le_sum hterm
        _ = (∑ j ∈ J, (1 / Real.sqrt 2) ^ j) * (Cd * dyadicBudget X P.r) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => by ring
        _ ≤ 4 * (Cd * dyadicBudget X P.r) := mul_le_mul_of_nonneg_right hgeom (by positivity)
        _ = 4 * Cd * dyadicBudget X P.r := by ring
    -- Bound `1 ≤ 2^48 * dyadicBudget X P.r`.
    have hone_le : (1 : ℝ) ≤ (2 : ℝ) ^ 48 * dyadicBudget X P.r := by
      unfold dyadicBudget
      have htot16 := div_totient_le_rpow_sixteenth P.r hr
      have hrtot_pos : (0 : ℝ) < P.r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
      have htot_lo : (1 / ((2 : ℝ) ^ 16 * (P.r : ℝ) ^ ((1 : ℝ) / 16))) ≤ (P.r.totient : ℝ) / (P.r : ℝ) := by
        have hinv := one_div_le_one_div_of_le (div_pos hr_pos hrtot_pos) htot16
        rwa [one_div_div] at hinv
      have htot3 : 1 / ((2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16)) ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 := by
        calc 1 / ((2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16))
            = (1 / ((2 : ℝ) ^ 16 * (P.r : ℝ) ^ ((1 : ℝ) / 16))) ^ 3 := by
              rw [one_div_pow, mul_pow, ← Real.rpow_natCast ((P.r : ℝ) ^ ((1 : ℝ) / 16)) 3,
                  ← Real.rpow_mul hr_pos.le]; norm_num
          _ ≤ ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) htot_lo 3
      have hsqrt_ge : (P.r : ℝ) ≤ Real.sqrt ((X : ℝ) * (P.r : ℝ)) := by
        rw [Real.le_sqrt hr_pos.le (by positivity)]
        have : (P.r : ℝ) ≤ X := Nat.cast_le.mpr hrX
        nlinarith
      have hlog3 : (1 : ℝ) ≤ (Real.log (2 * (X : ℝ))) ^ 3 := by
        have hlog1 : (1 : ℝ) ≤ Real.log (2 * (X : ℝ)) := one_le_log_two_mul (by omega)
        calc (1 : ℝ) = 1 ^ 3 := by norm_num
          _ ≤ (Real.log (2 * (X : ℝ))) ^ 3 := pow_le_pow_left₀ zero_le_one hlog1 3
      have hr_exp : (P.r : ℝ) ^ ((3 : ℝ) / 16) ≤ (P.r : ℝ) := by
        calc (P.r : ℝ) ^ ((3 : ℝ) / 16) ≤ (P.r : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hr) (by norm_num)
          _ = (P.r : ℝ) := Real.rpow_one _
      have hcore : (1 : ℝ) ≤ (2 : ℝ) ^ 48 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ))) := by
        have h1 : (P.r : ℝ) / ((2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16)) ≤
            ((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ)) := by
          have := mul_le_mul htot3 hsqrt_ge hr_pos.le (by positivity)
          rw [one_div_mul_eq_div] at this
          exact this
        have h2 : (1 : ℝ) / (2 : ℝ) ^ 48 ≤ (P.r : ℝ) / ((2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have : (2 : ℝ) ^ 48 * (P.r : ℝ) ^ ((3 : ℝ) / 16) ≤ (2 : ℝ) ^ 48 * (P.r : ℝ) :=
            mul_le_mul_of_nonneg_left hr_exp (by positivity)
          linarith
        have h3 := mul_le_mul_of_nonneg_left (h2.trans h1) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ 48)
        have h4 : (2 : ℝ) ^ 48 * (1 / (2 : ℝ) ^ 48) = 1 := by field_simp
        linarith
      calc (1 : ℝ) ≤ (2 : ℝ) ^ 48 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ))) := hcore
        _ ≤ (2 : ℝ) ^ 48 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ))) *
            (Real.log (2 * (X : ℝ))) ^ 3 := le_mul_of_one_le_right (by positivity) hlog3
        _ = (2 : ℝ) ^ 48 * (((P.r.totient : ℝ) / (P.r : ℝ)) ^ 3 * Real.sqrt ((X : ℝ) * (P.r : ℝ)) *
            (Real.log (2 * (X : ℝ))) ^ 3) := by ring
    have hbud_nn : 0 ≤ dyadicBudget X P.r := by
      unfold dyadicBudget
      have hlog_nn : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg (by
        have : (3 : ℝ) ≤ X := Nat.cast_le.mpr hX; linarith)
      positivity
    calc ((exceptions P X).card : ℝ) = (E_lo.card : ℝ) + (E_hi.card : ℝ) := by exact_mod_cast hcard_split
      _ ≤ 1 + 4 * Cd * dyadicBudget X P.r := add_le_add (by exact_mod_cast hlo_le) hhi_card
      _ ≤ (2 : ℝ) ^ 48 * dyadicBudget X P.r + 4 * Cd * dyadicBudget X P.r := add_le_add hone_le le_rfl
      _ = ((2 : ℝ) ^ 48 + 4 * Cd) * dyadicBudget X P.r := by ring
      _ ≤ C_final * dyadicBudget X P.r := mul_le_mul_of_nonneg_right (le_max_right _ _) hbud_nn

/-- **Stage 1 Main Theorem (`SmoothedTwistEstimate → Target`):**
Assuming the single-log smoothed twisted explicit-formula bound `SmoothedTwistEstimate`
(which follows from `DirichletGRH`), there exists an absolute constant `C > 0` such that
for EVERY `X ≥ 3`, EVERY positive integer modulus `1 ≤ r ≤ X`, and EVERY pair of coprime
residue classes `b₁, b₂ mod r`,
`E_r(X; b₁, b₂) ≤ C * min (X / r) ((φ(r) / r)³ * √(X * r) * log³(2 * X))`. -/
theorem target_of_smoothedTwistEstimate : SmoothedTwistEstimate → Target :=
  fun h => target_of_dyadicBound (dyadicBound_of_smoothedTwistEstimate h)

end GlobalTarget

end FareyGoldbach
