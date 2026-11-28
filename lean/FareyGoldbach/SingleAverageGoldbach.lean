import FareyGoldbach.SingleAverageAssembly
import FareyGoldbach.SingleAverageCore
import FareyGoldbach.SingleAverageMixed

open scoped BigOperators Classical

namespace FareyGoldbach

/-- Reduce the single-average exception count to a first averaged energy and a
uniform estimate for the fixed-class remainder against each model. -/
theorem routeA_single_dyadic_of_energies {Y r : ℕ} (hr : 0 < r) (hH26 : 2 ^ 26 ≤ Y / r)
    (b₁ : ReducedClass r) {U V : ℝ}
    (h₁ : (1 / (r.totient : ℝ)) * ∑ b₂ ∈ coprimeClasses r,
      (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b₁.1 Y α‖ ^ 2 * ‖routeARemainder r b₂ Y α‖ ^ 2) ≤ U)
    (h₂ : ∀ b₂ ∈ coprimeClasses r, (∫ α in (0 : ℝ)..1, ‖routeARemainder r b₁.1 Y α‖ ^ 2 *
      ‖modelSum r b₂ Y (routeAQ Y r) (routeAQ Y r) α‖ ^ 2) ≤ V) :
    singleAvgDyadicExceptions Y r hr b₁ *
      ((1 / 262144 : ℝ) * ((r : ℝ) / r.totient) ^ 2 * ((Y : ℝ) / r)) ^ 2 ≤ 2 * (U + V) := by
  let T : ℝ := (1 / 262144 : ℝ) * ((r : ℝ) / r.totient) ^ 2 * ((Y : ℝ) / r)
  let I₁ : ℕ → ℝ := fun b₂ =>
    ∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b₁.1 Y α‖ ^ 2 * ‖routeARemainder r b₂ Y α‖ ^ 2
  let E : ReducedClass r → ℝ := fun b₂ =>
    ((dyadicExceptions ⟨r, hr, b₁.1, b₂.1, (mem_coprimeClasses.mp b₁.2).1,
      (mem_coprimeClasses.mp b₂.2).1, (mem_coprimeClasses.mp b₁.2).2,
      (mem_coprimeClasses.mp b₂.2).2⟩ Y).card : ℝ)
  have ht : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ht' : 0 ≤ 1 / (r.totient : ℝ) := by positivity
  change ((1 / (r.totient : ℝ)) * ∑ b₂ ∈ (coprimeClasses r).attach, E b₂) * T ^ 2 ≤ _
  rw [mul_assoc, Finset.sum_mul]
  calc (1 / (r.totient : ℝ)) * ∑ b₂ ∈ (coprimeClasses r).attach, E b₂ * T ^ 2
      ≤ (1 / (r.totient : ℝ)) * ∑ b₂ ∈ (coprimeClasses r).attach, (2 * (I₁ b₂.1 + V)) := by
        apply mul_le_mul_of_nonneg_left _ ht'
        refine Finset.sum_le_sum fun b₂ _ => ?_
        exact (routeA_dyadic_pair_split hr hH26 b₁ b₂).trans
          (by linarith only [h₂ b₂.1 b₂.2])
    _ = 2 * ((1 / (r.totient : ℝ)) * (∑ b₂ ∈ coprimeClasses r, I₁ b₂) + V) := by
      rw [Finset.sum_attach (coprimeClasses r) (fun b₂ => 2 * (I₁ b₂ + V)), ← Finset.mul_sum,
        Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_coprimeClasses]
      field_simp
    _ ≤ _ := by linarith only [h₁]

/-- The cutoff-sensitive single-average estimate on one active dyadic interval. -/
theorem single_average_dyadic_of_smoothedTwist (h : SmoothedTwistEstimate) :
    SingleAverageDyadicBound := by
  obtain ⟨C, hC, hTw⟩ := h
  obtain ⟨M, hM, hmix⟩ := fixed_mixed_integral_bounds hC hTw (74 + 4 * C) (by positivity)
  let F : ℝ := (3 * (3 * C + 1) ^ 2 * (2 : ℝ) ^ 15 + 3 + 3 * (2 : ℝ) ^ 39) * (1 + 2 * C)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  set J : ℝ := 2 * (262144 : ℝ)^2
  refine ⟨J * (F + M), by dsimp [J]; positivity, ?_⟩
  intro r Y hr b₁ hH hB D hD
  dsimp only
  have hH26 : 2 ^ 26 ≤ Y / r := le_trans (by norm_num) hH
  have hYn : 0 < Y := lt_of_lt_of_le (Nat.mul_pos hr (by norm_num))
    ((Nat.mul_le_mul_left r hH).trans (Nat.mul_div_le Y r))
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have ht' : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hY' : (0 : ℝ) < Y := Nat.cast_pos.mpr hYn
  have hD' : (0 : ℝ) < D := Nat.cast_pos.mpr (by omega)
  set H : ℝ := (Y : ℝ) / r
  set L := Real.log (2 * (Y : ℝ))
  set a : ℝ := (r.totient : ℝ) / r
  set κ : ℝ := (r : ℝ) / r.totient
  set G : ℝ := κ^4 * H^2
  have hH' : 0 < H := div_pos hY' hr'
  have ha' : 0 < a := div_pos ht' hr'
  have hκ' : 0 < κ := div_pos hr' ht'
  have hG : 0 < G := by dsimp [G]; positivity
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * Y))
  have hLD : 0 ≤ Real.log (2 * (D : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * D))
  let u := a^2 * Real.sqrt H * L^3
  let v₀ := a^2 * (r : ℝ) * L^2 * Real.log (2 * (D : ℝ)) + a * H * L / (D : ℝ)^2
  let v₁ := a^3 * (r : ℝ) * L^3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv₀ : 0 ≤ v₀ := by dsimp [v₀]; positivity
  have hv₁ : 0 ≤ v₁ := by dsimp [v₁]; positivity
  have hκa : κ * a = 1 := by dsimp [κ, a]; field_simp
  have hYr : (Y : ℝ) = (r : ℝ) * H := by dsimp [H]; field_simp
  have hκa₂ : κ^2 * a^2 = 1 := by rw [← mul_pow, hκa, one_pow]
  have hκa₃ : κ^3 * a^3 = 1 := by rw [← mul_pow, hκa, one_pow]
  have heU : κ^2 * H^2 * Real.sqrt H * L^3 = G * u := by
    dsimp [G, u]
    calc _ = κ^2 * H^2 * Real.sqrt H * L^3 * (κ^2 * a^2) := by rw [hκa₂, mul_one]
      _ = _ := by ring
  have heV₀ : κ^2 * (Y : ℝ) * H * L^2 * Real.log (2 * (D : ℝ)) +
      κ^3 * H^3 * L / (D : ℝ)^2 = G * v₀ := by
    have h₀ : κ^2 * (Y : ℝ) * H * L^2 * Real.log (2 * (D : ℝ)) =
        G * (a^2 * (r : ℝ) * L^2 * Real.log (2 * (D : ℝ))) := by
      rw [hYr]
      dsimp [G]
      calc _ = κ^2 * (r : ℝ) * H^2 * L^2 * Real.log (2 * (D : ℝ)) * (κ^2 * a^2) := by
              rw [hκa₂, mul_one]; ring
        _ = _ := by ring
    have h₁ : κ^3 * H^3 * L = G * (a * H * L) := by
      dsimp [G]
      calc _ = (κ^3 * H^3 * L) * (κ * a) := by rw [hκa, mul_one]
        _ = _ := by ring
    dsimp [v₀]
    rw [h₀, h₁, mul_add, mul_div_assoc]
  have heV₁ : κ * (Y : ℝ) * H * L^3 = G * v₁ := by
    rw [hYr]
    dsimp [G, v₁]
    calc _ = κ * (r : ℝ) * H^2 * L^3 * (κ^3 * a^3) := by rw [hκa₃, mul_one]; ring
      _ = _ := by ring
  have hmixed : ∀ b₂ ∈ coprimeClasses r,
      (∫ α in (0 : ℝ)..1, ‖routeARemainder r b₁.1 Y α‖ ^ 2 *
        ‖modelSum r b₂ Y (routeAQ Y r) (routeAQ Y r) α‖ ^ 2) ≤
        M * (G * min v₀ v₁) := by
    intro b₂ hb₂
    have ht := (routeA_fixed_l2 hC hTw hr (mem_coprimeClasses.mp b₁.2).1
      (mem_coprimeClasses.mp b₁.2).2 hH hB).2
    obtain ⟨hlo, hhi⟩ := hmix hr (mem_coprimeClasses.mp b₁.2).1
      (mem_coprimeClasses.mp b₁.2).2 (mem_coprimeClasses.mp hb₂).1 hH ht D hD
    change _ ≤ M * (κ^2 * (Y : ℝ) * H * L^2 * Real.log (2 * (D : ℝ)) +
      κ^3 * H^3 * L / (D : ℝ)^2) at hlo
    change _ ≤ M * (κ * (Y : ℝ) * H * L^3) at hhi
    rw [heV₀] at hlo
    rw [heV₁] at hhi
    rcases le_total v₀ v₁ with h | h
    · simpa only [routeARemainder, min_eq_left h] using hlo
    · simpa only [routeARemainder, min_eq_right h] using hhi
  have hfirst := routeA_first_energy hC hTw hr (mem_coprimeClasses.mp b₁.2).1
    (mem_coprimeClasses.mp b₁.2).2 hH hB
  change _ ≤ F * (κ^2 * H^2 * Real.sqrt H * L^3) at hfirst
  rw [heU] at hfirst
  have h := routeA_single_dyadic_of_energies hr hH26 b₁ hfirst hmixed
  have hv : 0 ≤ min v₀ v₁ := le_min hv₀ hv₁
  change singleAvgDyadicExceptions Y r hr b₁ ≤ (J * (F + M)) * (u + min v₀ v₁)
  apply le_of_mul_le_mul_right _ hG
  calc singleAvgDyadicExceptions Y r hr b₁ * G =
      (262144 : ℝ)^2 * (singleAvgDyadicExceptions Y r hr b₁ * ((1/262144 : ℝ) * κ^2 * H)^2) := by
        dsimp [G]; ring
    _ ≤ (262144 : ℝ)^2 * (2 * (F * (G * u) + M * (G * min v₀ v₁))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = J * (F * u + M * min v₀ v₁) * G := by dsimp [J]; ring
    _ ≤ (J * (F + M) * (u + min v₀ v₁)) * G := by
      have hx := mul_nonneg hF hv
      have hy := mul_nonneg hM.le hu
      have hx' : F * u + M * min v₀ v₁ ≤ (F + M) * (u + min v₀ v₁) := by
        nlinarith only [hx, hy]
      exact mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hx' (by dsimp [J]; positivity)).trans_eq (by ring)) hG.le

/-- The sharp cutoff bound with a single fixed reduced residue class. -/
theorem single_average_sharp_of_smoothedTwist (h : SmoothedTwistEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgSharpBudget X r :=
  singleAvgSharp_of_dyadic (single_average_dyadic_of_smoothedTwist h)

theorem single_average_sharp_of_dirichletGRH (h : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgSharpBudget X r :=
  single_average_sharp_of_smoothedTwist (smoothedTwistEstimate_of_dirichletGRH h)

/-- The single-average power bound obtained from the sharp logarithmic bound. -/
theorem single_average_of_smoothedTwist (h : SmoothedTwistEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgPowerBudget X r :=
  singleAvgPower_of_dyadic (single_average_dyadic_of_smoothedTwist h)

theorem single_average_of_dirichletGRH (h : DirichletGRH) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X r : ℕ) (hr : 0 < r) (b₁ : ReducedClass r), 2 ≤ X → r ≤ X →
      singleAvgExceptions X r hr b₁ ≤ C * singleAvgPowerBudget X r :=
  single_average_of_smoothedTwist (smoothedTwistEstimate_of_dirichletGRH h)

end FareyGoldbach
