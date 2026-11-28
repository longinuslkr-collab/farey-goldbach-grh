import FareyGoldbach.TwinChenConditional
import FareyGoldbach.TwinChenPrimeDistribution
import FareyGoldbach.TwinChenSwitchDistribution
import FareyGoldbach.ChenAPExplicitMargin

/-! # Unconditional twin Chen counting and infinitude -/

open Filter Finset
open scoped Topology Classical

namespace FareyGoldbach

theorem twinChen_bounded_count_lower_unconditional :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      c*(X:ℝ)/Real.log (X:ℝ)^2 ≤
        ((X.primesLE.filter (fun p => IsAlmostPrimeTwoBounded (199/100:ℝ) (p+2))).card:ℝ) := by
  obtain ⟨c,hc,h⟩ := twinChen_bounded_count_lower_of_distributions (δ:=0) (θ:=4999/10000)
    (η:=9/2000) (εcut:=1/2000) (α:=199/100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    chen_margin_gt_balanced_loss_unconditional
    (twinChenPrimeDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (twinChenClassicDistributionAt_zero_unconditional (by norm_num) (by norm_num))
    (twinChenBoundedDistributionAt_zero_unconditional (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with X h
  simpa [twinChenBoundedRepresentations,Nat.mod_one] using
    h 1 0 (by decide) (by simp) (by decide) (by decide)

private theorem bounded_isAlmostPrimeTwo {α : ℝ} {m : ℕ} (h : IsAlmostPrimeTwoBounded α m) :
    IsAlmostPrimeTwo m := by
  rcases h with hp | ⟨p,q,hp,hq,hm,_⟩
  · exact Or.inr (Or.inl hp)
  · exact Or.inr (Or.inr ⟨p,q,hp,hq,hm⟩)

theorem twinChen_count_lower_unconditional :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ X : ℕ in atTop,
      c*(X:ℝ)/Real.log (X:ℝ)^2 ≤
        ((X.primesLE.filter (fun p => IsAlmostPrimeTwo (p+2))).card:ℝ) := by
  obtain ⟨c,hc,h⟩ := twinChen_bounded_count_lower_unconditional
  refine ⟨c,hc,?_⟩
  filter_upwards [h] with X h
  exact h.trans (Nat.cast_le.mpr (Finset.card_le_card fun p hp =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,bounded_isAlmostPrimeTwo (Finset.mem_filter.mp hp).2⟩))

theorem twinChen_bounded_infinite_unconditional :
    ∀ B : ℕ, ∃ p : ℕ, B<p ∧ p.Prime ∧ IsAlmostPrimeTwoBounded (199/100:ℝ) (p+2) := by
  intro B
  obtain ⟨c,hc,h⟩ := twinChen_bounded_count_lower_unconditional
  have hscale := chenAPLogScale_eventually_gt (δ:=0) (c:=((B:ℝ)+1)/c)
    (by norm_num) (by positivity)
  have hlarge : ∀ᶠ X : ℕ in atTop, (B:ℝ)+1<c*chenAPLogScale X 1 := by
    filter_upwards [hscale] with X hX
    have ht := (div_lt_iff₀ hc).mp (hX 1 (by decide) (by simp))
    rwa [mul_comm] at ht
  obtain ⟨X,hBig,hCount⟩ := (hlarge.and h).exists
  let S := X.primesLE.filter (fun p => IsAlmostPrimeTwoBounded (199/100:ℝ) (p+2))
  have h₁ : (B:ℝ)+1<(S.card:ℝ) := hBig.trans_le (by
    simpa [chenAPLogScale,←mul_div_assoc,S] using hCount)
  have h₂ : B+1<S.card := by exact_mod_cast h₁
  have hp : ∃ p∈S, B<p := by
    by_contra! hm
    have hs : S⊆Finset.range (B+1) := by
      intro p hp
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm p hp))
    have hbound := Finset.card_le_card hs
    rw [Finset.card_range] at hbound
    exact (not_le_of_gt h₂) hbound
  obtain ⟨p,hp,hBp⟩ := hp
  obtain ⟨hpr,ha⟩ := Finset.mem_filter.mp hp
  exact ⟨p,hBp,(Nat.mem_primesLE.mp hpr).2,ha⟩

theorem twinChen_infinite_unconditional :
    ∀ B : ℕ, ∃ p : ℕ, B<p ∧ p.Prime ∧ IsAlmostPrimeTwo (p+2) := by
  intro B
  obtain ⟨p,hp,hpr,ha⟩ := twinChen_bounded_infinite_unconditional B
  exact ⟨p,hp,hpr,bounded_isAlmostPrimeTwo ha⟩

end FareyGoldbach
