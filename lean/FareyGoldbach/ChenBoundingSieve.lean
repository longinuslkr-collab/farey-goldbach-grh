import FareyGoldbach.ChenConditional
import FareyGoldbach.ChenSieveNormalization
import FareyGoldbach.BoundingSieveImport

/-! # The Chen local densities as a Mathlib bounding sieve -/

namespace FareyGoldbach

noncomputable def chenArithmeticDensity : ArithmeticFunction ℝ where
  toFun := chenDivisorDensity
  map_zero' := by simp [chenDivisorDensity]

@[simp] theorem chenArithmeticDensity_apply (d : ℕ) :
    chenArithmeticDensity d = chenDivisorDensity d := rfl

theorem chenArithmeticDensity_multiplicative : chenArithmeticDensity.IsMultiplicative := by
  constructor
  · simp [chenDivisorDensity]
  · intro m n h
    simp [chenDivisorDensity, Nat.totient_mul h, Nat.cast_mul, mul_comm]

theorem three_le_of_mem_chenSiftingPrimes {N z p : ℕ} (he : Even N)
    (hp : p ∈ chenSiftingPrimes N z) : 3 ≤ p := by
  obtain ⟨_,hp,hN⟩ := Finset.mem_filter.mp hp
  have h2 := hp.two_le
  have he' : 2 ∣ N := even_iff_two_dvd.mp he
  by_contra! hh
  exact hN (by rwa [show p=2 by omega])

/-- The carrier of sieve polynomials with the local density for Chen's problem.
Its mass and sequence weights are unused in the main polynomials. -/
noncomputable def chenBoundingSieve {N : ℕ} (he : Even N) (z : ℕ) : BoundingSieve where
  support := ∅
  prodPrimes := chenSiftingProduct N z
  prodPrimes_squarefree := chenSiftingProduct_squarefree N z
  weights := 0
  weights_nonneg := by simp
  totalMass := 0
  nu := chenArithmeticDensity
  nu_mult := chenArithmeticDensity_multiplicative
  nu_pos_of_prime := by
    intro p hp _
    exact one_div_pos.mpr (Nat.cast_pos.mpr (Nat.totient_pos.mpr hp.pos))
  nu_lt_one_of_prime := by
    intro p hp hd
    have hP := (chenSiftingProduct_squarefree N z).ne_zero
    have hp' : p ∈ chenSiftingPrimes N z := by
      rw [← chenSiftingProduct_primeFactors]
      exact Nat.mem_primeFactors.mpr ⟨hp,hd,hP⟩
    have hp₃ := three_le_of_mem_chenSiftingPrimes he hp'
    change (1:ℝ)/(p.totient:ℝ)<1
    rw [Nat.totient_prime hp]
    have h1 : (1:ℝ) < (p-1:ℕ) := by exact_mod_cast (show 1<p-1 by omega)
    exact (div_lt_iff₀ (by linarith : (0:ℝ)<(p-1:ℕ))).mpr (by simpa using h1)

@[simp] theorem chenBoundingSieve_nu {N : ℕ} (he : Even N) (z d : ℕ) :
    (chenBoundingSieve he z).nu d = chenDivisorDensity d := rfl

@[simp] theorem chenBoundingSieve_prodPrimes {N : ℕ} (he : Even N) (z : ℕ) :
    (chenBoundingSieve he z).prodPrimes = chenSiftingProduct N z := rfl

theorem chenSiftingPrime_lt_cutoff {N z p : ℕ} (hp : p ∈ chenSiftingPrimes N z) : p < z :=
  Finset.mem_range.mp (Finset.mem_filter.mp hp).1

end FareyGoldbach
