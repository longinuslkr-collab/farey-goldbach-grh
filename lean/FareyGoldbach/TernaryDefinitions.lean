import FareyGoldbach.Defs

/-! # Ternary Goldbach representations in prescribed residue classes -/

open scoped Classical

namespace FareyGoldbach

/-- Ordered prime triples in the three prescribed residue classes. -/
noncomputable def ternaryRepresentations (r b₁ b₂ b₃ n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 2 n).product ((Finset.Icc 2 n).product (Finset.Icc 2 n))).filter fun p =>
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.Prime ∧ p.1+p.2.1+p.2.2=n ∧
      p.1%r=b₁ ∧ p.2.1%r=b₂ ∧ p.2.2%r=b₃

def ternaryAdmissible (r b₁ b₂ b₃ n : ℕ) : Prop :=
  Odd n ∧ n%r=(b₁+b₂+b₃)%r

def ternaryGoodBlock (X r b₁ b₂ b₃ : ℕ) : Prop :=
  ∀ n ∈ Finset.Ioc (X/2) X, ternaryAdmissible r b₁ b₂ b₃ n →
    (ternaryRepresentations r b₁ b₂ b₃ n).Nonempty

/-- Removing a prime from this interval leaves a binary target above `X/4`. -/
noncomputable def ternaryCandidatePrimes (X r b : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (X/4)).filter fun p => p.Prime ∧ p%r=b

end FareyGoldbach
