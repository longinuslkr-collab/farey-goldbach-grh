import FareyGoldbach.PrimeNumberTheoremUnconditional
import FareyGoldbach.ChenTheoremOfSmallConductor

/-! # Unconditional distribution estimates and Chen's theorem -/

open Filter
open scoped Topology

namespace FareyGoldbach

theorem bombieri_vinogradov_unconditional : ChenPrimitiveMangoldtBV :=
  bombieri_vinogradov_of_smallConductor smallConductorPrimeTwists_unconditional

theorem chenPrimeAPDistribution_unconditional : ChenPrimeAPDistribution :=
  chenPrimeAPDistribution_of_pnt_and_primitiveMangoldt primeCounting_ratio_unconditional
    bombieri_vinogradov_unconditional

theorem chenSwitchingDistribution_unconditional : ChenSwitchingDistribution :=
  chenSwitchingDistribution_of_pnt_and_smallConductor primeCounting_ratio_unconditional
    smallConductorPrimeTwists_unconditional

theorem chen_count_lower_unconditional :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ N : ℕ in atTop, Even N →
      c*(N:ℝ)/Real.log (N:ℝ)^2≤(chenCount N:ℝ) :=
  chen_count_lower_of_distributions chenPrimeAPDistribution_unconditional
    chenSwitchingDistribution_unconditional

theorem chen_theorem_unconditional :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ p+m=N :=
  chen_theorem_of_distributions chenPrimeAPDistribution_unconditional
    chenSwitchingDistribution_unconditional

/-- The quantitative estimate also guarantees a complement greater than one. -/
theorem chen_theorem_unconditional_nontrivial :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∃ p m : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1<m ∧ p+m=N := by
  obtain ⟨c,hc,hcount⟩ := chen_count_lower_unconditional
  have hlim : Tendsto (fun N : ℕ => Real.log (N:ℝ)^2/(N:ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (by norm_num : (0:ℝ)<1)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [Function.comp_def,Real.rpow_two,Real.rpow_one] using h
  filter_upwards [hcount,hlim.eventually_lt_const (by positivity : 0<c/2),
    eventually_ge_atTop (2:ℕ)] with N hN hratio hN₂
  intro heven
  have hp : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hl : 0<Real.log (N:ℝ) := Real.log_pos (Nat.one_lt_cast.mpr hN₂)
  have htwo : (2:ℝ)<c*N/Real.log N^2 := (lt_div_iff₀ (sq_pos_of_pos hl)).mpr
    (by linarith only [(div_lt_iff₀ hp).mp hratio])
  have hcard : 2<chenCount N := Nat.cast_lt.mp (show (2:ℝ)<(chenCount N:ℝ) from htwo.trans_le (hN heven))
  classical
  let S := (chenA N).filter IsAlmostPrimeTwo
  have hex : ∃ m∈S, 1<m := by
    by_contra! h
    have hsub : S⊆Finset.range 2 := fun m hm => Finset.mem_range.mpr (by have := h m hm; omega)
    have hs : S.card≤2 := (Finset.card_le_card hsub).trans_eq (Finset.card_range 2)
    exact (not_lt_of_ge hs) hcard
  obtain ⟨m,hm,hlarge⟩ := hex
  obtain ⟨hA,halmost⟩ := Finset.mem_filter.mp hm
  obtain ⟨hbound,hprime⟩ := Finset.mem_filter.mp hA
  exact ⟨N-m,m,hprime,halmost,hlarge,Nat.sub_add_cancel (by have := Finset.mem_range.mp hbound; omega)⟩

end FareyGoldbach
