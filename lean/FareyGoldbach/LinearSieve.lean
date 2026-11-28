import FareyGoldbach.LinearSieveWeights
import FareyGoldbach.LinearSieveFactors

/-! # The finite linear sieve with an unsigned distribution error -/

namespace FareyGoldbach

open scoped Classical

/-- Coefficients extended by zero outside the divisors of the sifting product. -/
noncomputable def linearSieveWeight (upper : Bool) (P D d : ℕ) : ℤ :=
  if d∣P then rosserWeight upper D d else 0

theorem linearSieveWeight_support {upper : Bool} {P D d : ℕ} (hw : linearSieveWeight upper P D d≠0) :
    Squarefree d ∧ d<D ∧ d∣P := by
  by_cases hd : d∣P
  · have hr : rosserWeight upper D d≠0 := by simpa [linearSieveWeight,hd] using hw
    exact ⟨by_contra fun h ↦ hr (rosserWeight_zero_of_not_squarefree h upper),
      lt_of_not_ge (fun h ↦ hr (rosserWeight_zero_of_level h upper)),hd⟩
  · exact (hw (by simp [linearSieveWeight,hd])).elim

theorem abs_linearSieveWeight_le_one (upper : Bool) (P D d : ℕ) :
    |linearSieveWeight upper P D d|≤1 := by
  unfold linearSieveWeight
  split
  · exact abs_rosserWeight_le_one upper D d
  · norm_num

theorem linearSieveWeight_on_divisors (upper : Bool) {P d : ℕ} (D : ℕ) (hd : d∈P.divisors) :
    linearSieveWeight upper P D d=rosserWeight upper D d := by
  simp [linearSieveWeight,Nat.dvd_of_mem_divisors hd]

/-- Rosser main term for the specified density function on squarefree moduli. -/
noncomputable def linearSieveMain (upper : Bool) (P D : ℕ) (g : ℕ→ℝ) : ℝ :=
  ∑ d ∈ P.divisors, (rosserWeight upper D d:ℝ)*g d

/-- The unweighted sum of absolute remainders, restricted to the actual sieve level. -/
noncomputable def linearSieveRemainder (P D : ℕ) (A : Finset ℕ) (X : ℝ) (g : ℕ→ℝ) : ℝ :=
  ∑ d ∈ P.divisors.filter (·<D), |((A.filter (d ∣ ·)).card:ℝ)-X*g d|

/-- For squarefree moduli, the progression density factors over their distinct primes. -/
theorem squarefree_totient_inv_eq_prod {d : ℕ} (hd : Squarefree d) :
    (d.totient:ℝ)⁻¹=∏ p∈d.primeFactors,((p:ℝ)-1)⁻¹ := by
  have hφ : d.totient=∏ p∈d.primeFactors,(p-1) := by
    rw [Nat.totient_eq_div_primeFactors_mul,Nat.prod_primeFactors_of_squarefree hd,
      Nat.div_self hd.ne_zero.bot_lt,one_mul]
  rw [hφ,Nat.cast_prod,← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le,Nat.cast_one]

/-- The Rosser packet for the local density `1/(p−1)` is exactly the main
term paired with the arithmetic progression errors at density `1/φ(d)`. -/
theorem linearSieveMain_inv_totient_eq_rosserPacket (upper : Bool) {P D : ℕ}
    (hP : Squarefree P) (hD : 1<D) (hprime : ∀p∈P.primeFactors,p<D) :
    linearSieveMain upper P D (fun d ↦ (d.totient:ℝ)⁻¹) =
      rosserPacket upper D 1 P.primeFactors (fun p ↦ ((p:ℝ)-1)⁻¹) := by
  rw [linearSieveMain,rosserPacket_eq_divisor_sum upper hD hP hprime]
  apply Finset.sum_congr rfl
  intro d hd
  rw [squarefree_totient_inv_eq_prod (hP.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd))]

private theorem sum_divisor_fibres (S A : Finset ℕ) (w : ℕ→ℤ) :
    (∑ a∈A, ∑ d∈S.filter (·∣a), w d) =
      ∑ d∈S, w d*((A.filter (d∣·)).card:ℤ) := by
  classical
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have h (a : ℕ) : (if d∣a then w d else 0) = w d*(if d∣a then (1:ℤ) else 0) := by
    by_cases hd : d∣a <;> simp [hd]
  simp_rw [h,← Finset.mul_sum,Finset.sum_boole]

/-- Double counting the pointwise divisor sandwich gives the finite cardinal bounds. -/
theorem rosser_finite_card_bounds {P D : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) (A : Finset ℕ) :
    (∑ d∈P.divisors, (rosserWeight false D d:ℝ)*((A.filter (d∣·)).card:ℝ)) ≤
      ((A.filter (·.Coprime P)).card:ℝ) ∧
    ((A.filter (·.Coprime P)).card:ℝ) ≤
      (∑ d∈P.divisors, (rosserWeight true D d:ℝ)*((A.filter (d∣·)).card:ℝ)) := by
  have h₁ := Finset.sum_le_sum (s:=A) (fun a _ ↦ (rosser_divisor_bounds (n:=a) hP hD hprime).1)
  have h₂ := Finset.sum_le_sum (s:=A) (fun a _ ↦ (rosser_divisor_bounds (n:=a) hP hD hprime).2)
  rw [sum_divisor_fibres,Finset.sum_boole] at h₁
  rw [sum_divisor_fibres,Finset.sum_boole] at h₂
  exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

/-- The discrepancy between a weighted divisor count and its main term is paid
by the unsigned distribution error. -/
theorem linearSieve_discrepancy_le (upper : Bool) (P D : ℕ) (A : Finset ℕ) (X : ℝ) (g : ℕ→ℝ) :
    |(∑ d∈P.divisors,(rosserWeight upper D d:ℝ)*((A.filter (d∣·)).card:ℝ)) -
      X*linearSieveMain upper P D g| ≤ linearSieveRemainder P D A X g := by
  classical
  let w (d : ℕ) := (rosserWeight upper D d:ℝ)
  let r (d : ℕ) := ((A.filter (d∣·)).card:ℝ)-X*g d
  have hdiff : (∑ d∈P.divisors,w d*((A.filter (d∣·)).card:ℝ)) - X*linearSieveMain upper P D g =
      ∑ d∈P.divisors,w d*r d := by
    rw [linearSieveMain,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    dsimp [w,r]
    ring
  have hcut : (∑ d∈P.divisors,w d*r d) = ∑ d∈P.divisors.filter (·<D),w d*r d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d<D
    · simp [hd]
    · simp [hd,w,rosserWeight_zero_of_level (not_lt.mp hd)]
  change |(∑ d∈P.divisors,w d*((A.filter (d∣·)).card:ℝ)) - _| ≤ _
  rw [hdiff,hcut]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro d _
  have hwd : |w d| ≤ 1 := by
    dsimp [w]
    exact_mod_cast abs_rosserWeight_le_one upper D d
  rw [abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hwd

/-- The lower and upper finite linear-sieve inequalities for an arbitrary real
mass and density model. -/
theorem linearSieveBounds {P D : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) (A : Finset ℕ) (X : ℝ) (g : ℕ→ℝ) :
    X*linearSieveMain false P D g - linearSieveRemainder P D A X g ≤
      ((A.filter (·.Coprime P)).card:ℝ) ∧
    ((A.filter (·.Coprime P)).card:ℝ) ≤
      X*linearSieveMain true P D g + linearSieveRemainder P D A X g := by
  obtain ⟨hlo,hhi⟩ := rosser_finite_card_bounds hP hD hprime A
  have h₁ := (abs_le.mp (linearSieve_discrepancy_le false P D A X g)).1
  have h₂ := (abs_le.mp (linearSieve_discrepancy_le true P D A X g)).2
  constructor <;> linarith only [hlo,hhi,h₁,h₂]

/-- Any numerical lower and upper estimates of the two Rosser density sums
transfer to the sifted count at the same finite level. -/
theorem linearSieveBounds_of_main_comparison {P D : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) (A : Finset ℕ) {X : ℝ} (hX : 0≤X) (g : ℕ→ℝ)
    {L U : ℝ} (hL : L≤linearSieveMain false P D g) (hU : linearSieveMain true P D g≤U) :
    X*L - linearSieveRemainder P D A X g ≤ ((A.filter (·.Coprime P)).card:ℝ) ∧
      ((A.filter (·.Coprime P)).card:ℝ) ≤ X*U + linearSieveRemainder P D A X g := by
  obtain ⟨hl,hu⟩ := linearSieveBounds hP hD hprime A X g
  exact ⟨(sub_le_sub_right (mul_le_mul_of_nonneg_left hL hX) _).trans hl,
    hu.trans (add_le_add (mul_le_mul_of_nonneg_left hU hX) le_rfl)⟩

/-- A lower Rosser main-term comparison gives the usual first-branch lower
sieve estimate, with the same density error and finite distribution bill. -/
theorem linearSieveLower_of_comparison {P D : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) (A : Finset ℕ) {X : ℝ} (hX : 0≤X) (g : ℕ→ℝ)
    {s V ε : ℝ} (hL : V*(linearSieveLowerFactor s-ε)≤linearSieveMain false P D g) :
    X*(V*(linearSieveLowerFactor s-ε))-linearSieveRemainder P D A X g ≤
      ((A.filter (·.Coprime P)).card:ℝ) :=
  (linearSieveBounds_of_main_comparison hP hD hprime A hX g hL le_rfl).1

/-- An upper Rosser main-term comparison gives the first-branch upper sieve
estimate. -/
theorem linearSieveUpper_of_comparison {P D : ℕ} (hP : Squarefree P) (hD : 1<D)
    (hprime : ∀p∈P.primeFactors,p<D) (A : Finset ℕ) {X : ℝ} (hX : 0≤X) (g : ℕ→ℝ)
    {s V ε : ℝ} (hU : linearSieveMain true P D g≤V*(linearSieveUpperFactor s+ε)) :
    ((A.filter (·.Coprime P)).card:ℝ) ≤
      X*(V*(linearSieveUpperFactor s+ε))+linearSieveRemainder P D A X g :=
  (linearSieveBounds_of_main_comparison hP hD hprime A hX g le_rfl hU).2

end FareyGoldbach
