import FareyGoldbach.ChenDistributionInterfaces

/-! # Exact Mertens normalization of the Chen local product -/

open scoped BigOperators Classical

namespace FareyGoldbach

def chenPrimesBelow (z : ℕ) : Finset ℕ := (Finset.Icc 1 (z-1)).filter Nat.Prime

noncomputable def chenMertensProduct (z : ℕ) : ℝ :=
  ∏ p ∈ chenPrimesBelow z, (1-1/(p:ℝ))

noncomputable def chenSingularAtCutoff (N z : ℕ) : ℝ :=
  ∏ p ∈ chenPrimesBelow z, (1+localFactor 1 N p)

noncomputable def chenDensityProduct (N z : ℕ) : ℝ :=
  ∏ p ∈ chenSiftingPrimes N z, (1-1/(p.totient:ℝ))

private theorem chen_factor_product {p N : ℕ} (hp : p.Prime) :
    (1-1/(p:ℝ))*(1+localFactor 1 N p) = if p∣N then 1 else 1-1/(p.totient:ℝ) := by
  have hp1 : ¬p∣1 := fun h => hp.ne_one (Nat.dvd_one.mp h)
  have hp' : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have hp₀ : (p:ℝ)≠0 := by linarith
  have hp₁ : (p:ℝ)-1≠0 := by linarith
  unfold localFactor
  rw [ite_eq_right hp1, Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  by_cases h : p∣N
  · simp only [h,ite_true]
    field_simp [hp₀,hp₁]; ring
  · simp only [h,ite_false]
    field_simp [hp₀,hp₁]; ring

/-- The finite Chen density product splits exactly into a Mertens product and
the truncated singular series, with the prime two included. -/
theorem chenDensityProduct_eq_mertens_mul_singular {N z : ℕ} (hz : 1≤z) :
    chenDensityProduct N z = chenMertensProduct z * chenSingularAtCutoff N z := by
  unfold chenMertensProduct chenSingularAtCutoff
  rw [←Finset.prod_mul_distrib]
  have ht : (∏ p ∈ chenPrimesBelow z, (1-1/(p:ℝ))*(1+localFactor 1 N p)) =
      ∏ p ∈ chenPrimesBelow z, if p∣N then 1 else 1-1/(p.totient:ℝ) :=
    Finset.prod_congr rfl (fun _ hp => chen_factor_product (Finset.mem_filter.mp hp).2)
  rw [ht]
  have h : (chenPrimesBelow z).filter (fun p => ¬p∣N) = chenSiftingPrimes N z := by
    ext p
    simp only [chenPrimesBelow,chenSiftingPrimes,Finset.mem_filter,Finset.mem_Icc,Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨_,hpz⟩,hp⟩,hpN⟩
      exact ⟨by omega,hp,hpN⟩
    · rintro ⟨hpz,hp,hpN⟩
      exact ⟨⟨⟨hp.pos,by omega⟩,hp⟩,hpN⟩
  unfold chenDensityProduct
  rw [←h,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro p _
  by_cases hp : p∣N <;> simp [hp]

theorem chenSingularAtCutoff_ge_half {N z : ℕ} (hN : Even N) (hz : 3≤z) :
    (1:ℝ)/2≤chenSingularAtCutoff N z :=
  finiteEulerProd_ge_half 1 N (z-1) hN (by omega)

end FareyGoldbach
