module

public import Mathlib.Data.Nat.PrimeFin

/-! # Rough numbers and almost primes -/

@[expose] public section

namespace FareyGoldbach

/-- Every prime factor of `m` is at least the integer cutoff `z`. -/
def IsRough (z m : ℕ) : Prop :=
  ∀ q ∈ m.primeFactors, z ≤ q

/-- A positive integer with at most three prime factors, counted with multiplicity. -/
def IsAlmostPrimeThree (m : ℕ) : Prop :=
  0 < m ∧ m.primeFactorsList.length ≤ 3

end FareyGoldbach
