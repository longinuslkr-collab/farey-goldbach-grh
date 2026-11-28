import FareyGoldbach.SiegelTheorem
import FareyGoldbach.ZeroFreeRegion

/-! # An unconditional zero-free region for every primitive character -/

open Complex
open scoped Classical

namespace FareyGoldbach

private theorem unified_region_of_real_gap {ε : ℝ}
    (hGap : ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → 1<q → χ^2=1 → ∀ β : ℝ,
        1-c*(q:ℝ)^(-ε)≤β → β<1 → χ.LFunction (β:ℂ)≠0) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ s : ℂ,
        1-min (c/Real.log (2*(q:ℝ)*(2+|s.im|))) (c*(q:ℝ)^(-ε)) ≤ s.re → entireL χ s≠0 := by
  obtain ⟨a,ha,hclass⟩ := classical_zero_free_region
  obtain ⟨b,hb,hreal⟩ := hGap
  let c := min a b
  refine ⟨c, lt_min ha hb, ?_⟩
  intro q _ χ hprim s hreg
  let L := Real.log (2*(q:ℝ)*(2+|s.im|))
  have hL : 0≤L := zero_le_one.trans (one_le_log_two_mul_d_mul q s.im)
  change 1-min (c/L) (c*(q:ℝ)^(-ε))≤s.re at hreg
  by_cases he : χ=1 ∨ χ^2≠1 ∨ s.im≠0
  · apply hclass q χ hprim s he
    change 1-a/L≤s.re
    exact (sub_le_sub_left ((min_le_left ..).trans
      (div_le_div_of_nonneg_right (min_le_left a b) hL)) 1).trans hreg
  · push Not at he
    obtain ⟨hn,hquad,him⟩ := he
    by_cases hβ : 1≤s.re
    · exact zeroFree_primitive_nonzero_right hprim hβ
    have hq : 1<q := by
      have hq₀ : q≠0 := NeZero.ne q
      by_contra! h
      have hq₁ : q=1 := by omega
      subst q
      exact hn (Subsingleton.elim ..)
    have hs : (s.re:ℂ)=s := by simpa only [him,Complex.ofReal_zero,zero_mul,add_zero] using Complex.re_add_im s
    have hre : 1-b*(q:ℝ)^(-ε)≤s.re :=
      (sub_le_sub_left ((min_le_right ..).trans
        (mul_le_mul_of_nonneg_right (min_le_right a b) (Real.rpow_nonneg (Nat.cast_nonneg _) _))) 1).trans hreg
    have hout := hreal q χ hprim hq hquad s.re hre (lt_of_not_ge hβ)
    rw [hs] at hout
    simpa only [entireL,ite_eq_right hn] using hout

/-- For every positive exponent, a single positive constant gives a
zero-free region for all primitive conductors and all heights. -/
theorem unconditional_zero_free_region (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ∀ s : ℂ,
        1-min (c/Real.log (2*(q:ℝ)*(2+|s.im|))) (c*(q:ℝ)^(-ε)) ≤ s.re → entireL χ s≠0 :=
  unified_region_of_real_gap (siegel_real_zero_gap ε hε)

end FareyGoldbach
