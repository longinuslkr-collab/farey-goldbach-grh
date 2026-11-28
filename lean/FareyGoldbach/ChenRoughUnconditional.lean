import FareyGoldbach.ChenTheoremUnconditional
import FareyGoldbach.ChenSwitchingScales

/-! # Unconditional rough Chen representations -/

open Filter

namespace FareyGoldbach

/-- The unconditional quantitative Chen bound with rough, squarefree complements. -/
theorem chen_rough_eighth_count_lower_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c * (N:ℝ) / Real.log (N:ℝ)^2 ≤ ((chenRoughRepresentations N (chenLowerCutoff N)).card:ℝ) :=
  chen_rough_count_lower_of_distributions_and_comparisons chenPrimeAPDistribution_unconditional
    chenSwitchingDistribution_unconditional (fun _ => chenRosserMainComparisons_unconditional)

/-- Every sufficiently large even integer has a rough, squarefree Chen representation. -/
theorem chen_rough_eighth_theorem_unconditional :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        IsRough (chenLowerCutoff N) m ∧ p + m = N := by
  obtain ⟨c, hc, hcount⟩ := chen_rough_eighth_count_lower_unconditional
  filter_upwards [hcount, eventually_ge_atTop (2 : ℕ)] with N hcount hN hEven
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hNpos : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < c * (N:ℝ) / Real.log (N:ℝ)^2 := by positivity
  obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le (hcount hEven)))
  obtain ⟨p, hp⟩ := mem_chenRoughRepresentations_iff.mp hm
  exact ⟨p, m, hp⟩

/-- A real power of any fixed exponent below one eighth is a valid roughness cutoff. -/
theorem chen_rough_eighth_rpow_theorem_unconditional {θ : ℝ} (hθ : θ < 1/8) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        (∀ q ∈ m.primeFactors, (N:ℝ)^θ ≤ (q:ℝ)) ∧ p + m = N := by
  have hpow := eventually_rpow_add_one_le_powerLevel
    (le_max_right θ 0) (max_lt hθ (by norm_num : (0:ℝ) < 1/8))
  filter_upwards [chen_rough_eighth_theorem_unconditional, hpow, eventually_ge_atTop (1 : ℕ)]
    with N hrep hpow hN hEven
  obtain ⟨p, m, hp, hP, hm, hsq, hcop, hr, heq⟩ := hrep hEven
  refine ⟨p, m, hp, hP, hm, hsq, hcop, ?_, heq⟩
  intro q hq
  change (N:ℝ)^(max θ 0) + 1 ≤ (chenLowerCutoff N:ℝ) at hpow
  calc
    (N:ℝ)^θ ≤ (N:ℝ)^(max θ 0) :=
      Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) (le_max_left θ 0)
    _ ≤ (N:ℝ)^(max θ 0) + 1 := le_add_of_nonneg_right zero_le_one
    _ ≤ (chenLowerCutoff N:ℝ) := hpow
    _ ≤ (q:ℝ) := Nat.cast_le.mpr (hr q hq)

end FareyGoldbach
