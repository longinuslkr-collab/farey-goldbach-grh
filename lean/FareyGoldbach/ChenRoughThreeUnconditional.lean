import FareyGoldbach.RoughGoldbachLowerSieve
import FareyGoldbach.RoughGoldbachFourFactors

/-! # Unconditional rough P₃ Goldbach representations -/

open Filter
open scoped Topology Classical

namespace FareyGoldbach

/-- The rough squarefree P₃ representations indexed by their complement `m`. -/
noncomputable def chenRoughThreeRepresentations (N z : ℕ) : Finset ℕ :=
  (chenA N).filter fun m ↦
    IsAlmostPrimeThree m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧ IsRough z m

theorem mem_chenRoughThreeRepresentations_iff {N z m : ℕ} :
    m ∈ chenRoughThreeRepresentations N z ↔
      ∃ p : ℕ, p.Prime ∧ IsAlmostPrimeThree m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        IsRough z m ∧ p + m = N := by
  constructor
  · intro hm
    obtain ⟨hA, hP, hm₁, hsq, hcop, hr⟩ := Finset.mem_filter.mp hm
    obtain ⟨hbound, hp⟩ := Finset.mem_filter.mp hA
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hbound)
    exact ⟨N - m, hp, hP, hm₁, hsq, hcop, hr, Nat.sub_add_cancel hmN⟩
  · rintro ⟨p, hp, hP, hm₁, hsq, hcop, hr, heq⟩
    have hA : m ∈ chenA N :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [show N - m = p by omega]⟩
    exact Finset.mem_filter.mpr ⟨hA, hP, hm₁, hsq, hcop, hr⟩

theorem chenRoughThreeRepresentations_antitone (N : ℕ) {z w : ℕ} (hzw : z ≤ w) :
    chenRoughThreeRepresentations N w ⊆ chenRoughThreeRepresentations N z := by
  intro m hm
  obtain ⟨hA, hP, h₁, hsq, hcop, hr⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hA, hP, h₁, hsq, hcop, fun q hq ↦ hzw.trans (hr q hq)⟩

private theorem chen_rough_three_clean_card_le {N z y : ℕ} (hz : N < z^5) :
    (chenRoughThreeClean N z y).card ≤
      (chenRoughThreeRepresentations N z).card + (chenRoughThreeFourFactors N z y).card := by
  have hsub : chenRoughThreeClean N z y ⊆
      chenRoughThreeRepresentations N z ∪ chenRoughThreeFourFactors N z y := by
    intro m hm
    obtain ⟨hmN, hp, hm₁, hsq, hcop, hr, hpy⟩ := mem_chenRoughThreeClean_iff.mp hm
    have hA : m ∈ chenA N := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    have hlen := chen_rough_three_factor_length_le_four hm₁ hmN hr hz
    apply Finset.mem_union.mpr
    by_cases hthree : m.primeFactorsList.length ≤ 3
    · exact Or.inl (Finset.mem_filter.mpr ⟨hA, ⟨by omega, hthree⟩, hm₁, hsq, hcop, hr⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hA, hm₁, hsq, hr, by omega, hpy⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem chen_rough_three_count_near_quarter {ε : ℝ} (hε : 0 < ε)
    (hε₀ : ε < (1:ℝ)/524288) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (ε/2) * (N:ℝ) / Real.log (N:ℝ)^2 ≤
        ((chenRoughThreeRepresentations N (chenPowerLevel (1/4-ε) N)).card:ℝ) := by
  have hclean := chen_rough_three_clean_count_lower hε hε₀
  have hfour := chen_rough_three_four_count_upper hε hε₀
  have hU := eventually_inf_principal.mp chenCanonicalU_eventually_ge_half
  have hbudget : (2:ℝ)^35 * ε^3 ≤ ε/8 := by
    have hs := pow_le_pow_left₀ hε.le hε₀.le 2
    have hs' : (2:ℝ)^35 * ε^2 ≤ (1:ℝ)/8 := by nlinarith only [hs]
    calc
      (2:ℝ)^35 * ε^3 = ((2:ℝ)^35 * ε^2) * ε := by ring
      _ ≤ (1/8) * ε := mul_le_mul_of_nonneg_right hs' hε.le
      _ = ε/8 := by ring
  filter_upwards [hclean, hfour, hU, eventually_rough_three_cutoff_geometry hε₀]
    with N hc hf hu hgeom hEven
  let z := chenPowerLevel (1/4-ε) N
  let y := chenPowerLevel (1/512) N + 1
  have hcard : ((chenRoughThreeClean N z y).card:ℝ) ≤
      ((chenRoughThreeRepresentations N z).card:ℝ) + ((chenRoughThreeFourFactors N z y).card:ℝ) := by
    exact_mod_cast chen_rough_three_clean_card_le (z := z) (y := y) hgeom.2
  have hU₀ : 0 ≤ chenCanonicalU N := le_trans (by norm_num) (hu hEven)
  have hscale : 0 ≤ chenSieveScale chenCanonicalU N := by unfold chenSieveScale; positivity
  have hfour' := (hf hEven).trans (mul_le_mul_of_nonneg_right hbudget hscale)
  have hmain : ε * chenSieveScale chenCanonicalU N ≤ ((chenRoughThreeRepresentations N z).card:ℝ) :=
    by nlinarith only [hcard, hc hEven, hfour', mul_nonneg hε.le hscale]
  refine le_trans ?_ hmain
  unfold chenSieveScale
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := mul_le_mul_of_nonneg_right (hu hEven) (Nat.cast_nonneg (α:=ℝ) N)
  nlinarith only [mul_le_mul_of_nonneg_left h hε.le]

/-- Quantitative unconditional rough P₃ Goldbach at each fixed real exponent below a quarter. -/
theorem chen_rough_three_count_lower_unconditional {θ : ℝ} (hθ : θ < 1/4) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c * (N:ℝ) / Real.log (N:ℝ)^2 ≤
        ((chenRoughThreeRepresentations N ⌈(N:ℝ)^θ⌉₊).card:ℝ) := by
  let a : ℝ := max θ 0
  let ε : ℝ := min (1/1048576) ((1/4 - a)/2)
  have ha : a < 1/4 := max_lt hθ (by norm_num)
  have hε : 0 < ε := lt_min (by norm_num) (by linarith)
  have hε₀ : ε < (1:ℝ)/524288 := (min_le_left _ _).trans_lt (by norm_num)
  have hab : a < 1/4 - ε := by
    have hεa : ε ≤ (1/4 - a)/2 := min_le_right _ _
    linarith
  refine ⟨ε/2, by positivity, ?_⟩
  have hcut := eventually_rpow_add_one_le_powerLevel (le_max_right θ 0) hab
  filter_upwards [chen_rough_three_count_near_quarter hε hε₀, hcut, eventually_ge_atTop (1:ℕ)]
    with N hcount hcut hN hEven
  have hzn : ⌈(N:ℝ)^θ⌉₊ ≤ chenPowerLevel (1/4-ε) N := by
    apply Nat.ceil_le.mpr
    exact (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hN) (le_max_left θ 0)).trans
      ((le_add_of_nonneg_right zero_le_one).trans hcut)
  exact (hcount hEven).trans (Nat.cast_le.mpr
    (Finset.card_le_card (chenRoughThreeRepresentations_antitone N hzn)))

/-- A real-power rough squarefree P₃ representation for every sufficiently large even integer. -/
theorem chen_rough_three_rpow_theorem_unconditional {θ : ℝ} (hθ : θ < 1/4) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeThree m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        (∀ q ∈ m.primeFactors, (N:ℝ)^θ ≤ (q:ℝ)) ∧ p + m = N := by
  obtain ⟨c, hc, hcount⟩ := chen_rough_three_count_lower_unconditional hθ
  filter_upwards [hcount, eventually_ge_atTop (2:ℕ)] with N hcount hN hEven
  have hlog : 0 < Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN)
  have hNpos : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < c * (N:ℝ) / Real.log (N:ℝ)^2 := by positivity
  obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.cast_pos.mp (hpos.trans_le (hcount hEven)))
  obtain ⟨p, hp, hP, hm₁, hsq, hcop, hr, heq⟩ := mem_chenRoughThreeRepresentations_iff.mp hm
  exact ⟨p, m, hp, hP, hm₁, hsq, hcop, fun q hq ↦ Nat.ceil_le.mp (hr q hq), heq⟩

end FareyGoldbach
