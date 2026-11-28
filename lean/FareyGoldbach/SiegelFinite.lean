import FareyGoldbach.LocalLogDerivative

/-! # A positive minimum for the finitely many low-conductor values at one -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem siegel_one_modulus {q : ℕ} [NeZero q] :
    ∃ c : ℝ, 0<c ∧ ∀ χ : DirichletCharacter ℂ q, χ≠1 → c≤‖χ.LFunction 1‖ := by
  classical
  let T := (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ≠1)
  let S := insert 1 (T.image fun χ => ‖χ.LFunction 1‖)
  have hS : S.Nonempty := ⟨1,mem_insert_self ..⟩
  have hpos (x : ℝ) (hx : x∈S) : 0<x := by
    rcases mem_insert.mp hx with rfl|h
    · exact zero_lt_one
    · obtain ⟨χ,hχ,rfl⟩ := mem_image.mp h
      exact norm_pos_iff.mpr (χ.LFunction_ne_zero_of_one_le_re (.inl (mem_filter.mp hχ).2) (by simp))
  refine ⟨S.min' hS,hpos _ (S.min'_mem hS),?_⟩
  intro χ hχ
  exact S.min'_le _ (mem_insert_of_mem (mem_image.mpr ⟨χ,mem_filter.mpr ⟨mem_univ _,hχ⟩,rfl⟩))

theorem siegel_small_moduli_L_one_lower (Q : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      q≤Q → χ≠1 → c≤‖χ.LFunction 1‖ := by
  induction Q with
  | zero =>
    refine ⟨1,zero_lt_one,?_⟩
    intro q _ χ hq _
    exact False.elim ((NeZero.ne q) (by omega))
  | succ Q ih =>
    obtain ⟨c,hc,hBound⟩ := ih
    obtain ⟨c',hc',hNext⟩ := siegel_one_modulus (q:=Q+1)
    refine ⟨min c c',lt_min hc hc',?_⟩
    intro q _ χ hq hχ
    by_cases he : q=Q+1
    · subst q
      exact (min_le_right ..).trans (hNext χ hχ)
    · exact (min_le_left ..).trans (hBound q χ (by omega) hχ)

end FareyGoldbach
