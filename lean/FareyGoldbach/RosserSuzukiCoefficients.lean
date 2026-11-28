import FareyGoldbach.RosserPrefixCalibration
import FareyGoldbach.LinearSieve
import MathlibNt.SieveTheory.LinearSieve.UpperRosserDensity

/-! # Agreement with the finite Suzuki/Iwaniec Rosser coefficients

The two definitions use descending integer prime chains and cardinalities of
inclusive prime prefixes, respectively. The identities below compare the actual
functions on each divisor of the sifting product.
-/

namespace FareyGoldbach

open MathlibNt.SieveTheory.LinearSieve

private theorem prefix_lower_iff (D : ℕ) (s : Finset ℕ) :
    rosserPrefixAdmits false D 1 s ↔ LowerRosserAdmissibleSet D s := by
  simp [rosserPrefixAdmits,LowerRosserAdmissibleSet]

private theorem prefix_upper_iff (D : ℕ) (s : Finset ℕ) :
    rosserPrefixAdmits true D 1 s ↔ UpperRosserAdmissibleSet D s := by
  simp [rosserPrefixAdmits,UpperRosserAdmissibleSet]

theorem rosserWeight_matches_suzuki_lower {P d D : ℕ} (hP : Squarefree P)
    (hd : d ∈ P.divisors) : (rosserWeight false D d : ℝ) = lowerRosserWeight P D d := by
  have hsq := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  by_cases hl : d < D
  · rw [rosserWeight,ite_eq_left ⟨hl,hsq⟩,rosserSubset_eq_prefix_weight]
    by_cases ht : LowerRosserAdmissibleSet D d.primeFactors <;>
      by_cases he : Even d.primeFactors.card <;>
      simp [lowerRosserWeight,LowerRosserAdmissible,prefix_lower_iff,ht,he,hd,hl]
  · simp [rosserWeight,lowerRosserWeight,hl]

theorem rosserWeight_matches_suzuki_upper {P d D : ℕ} (hP : Squarefree P)
    (hd : d ∈ P.divisors) : (rosserWeight true D d : ℝ) = upperRosserWeight P D d := by
  have hsq := hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
  by_cases hl : d < D
  · rw [rosserWeight,ite_eq_left ⟨hl,hsq⟩,rosserSubset_eq_prefix_weight]
    by_cases ht : UpperRosserAdmissibleSet D d.primeFactors <;>
      by_cases he : Even d.primeFactors.card <;>
      simp [upperRosserWeight,UpperRosserAdmissible,prefix_upper_iff,ht,he,hd,hl]
  · simp [rosserWeight,upperRosserWeight,hl]

theorem linearSieveMain_matches_suzuki_lower (S : BoundingSieve) (D : ℕ) :
    linearSieveMain false S.prodPrimes D S.nu = S.mainSum (lowerRosserWeight S.prodPrimes D) := by
  unfold linearSieveMain BoundingSieve.mainSum
  exact Finset.sum_congr rfl fun d hd =>
    congrArg (fun w : ℝ => w * S.nu d) (rosserWeight_matches_suzuki_lower S.prodPrimes_squarefree hd)

theorem linearSieveMain_matches_suzuki_upper (S : BoundingSieve) (D : ℕ) :
    linearSieveMain true S.prodPrimes D S.nu = S.mainSum (upperRosserWeight S.prodPrimes D) := by
  unfold linearSieveMain BoundingSieve.mainSum
  exact Finset.sum_congr rfl fun d hd =>
    congrArg (fun w : ℝ => w * S.nu d) (rosserWeight_matches_suzuki_upper S.prodPrimes_squarefree hd)

end FareyGoldbach