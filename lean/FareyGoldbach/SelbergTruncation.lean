import FareyGoldbach.SharpRankin

/-! # Truncating a finite sieve product -/

open scoped BigOperators Classical

namespace FareyGoldbach

/-- The weighted first moment of a sum over a random subset with independent
inclusion probabilities `g i / (1 + g i)`. -/
theorem subset_product_first_moment {ι : Type*} (s : Finset ι) (g f : ι → ℝ)
    (hg : ∀ i ∈ s, 0 ≤ g i) :
    (∑ t ∈ s.powerset, (∏ i ∈ t, g i) * (∑ i ∈ t, f i)) =
      (∏ i ∈ s, (1 + g i)) * (∑ i ∈ s, (g i / (1 + g i)) * f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, 0 ≤ g i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have ha' : 0 < 1 + g a := by linarith [hg a (Finset.mem_insert_self a s)]
    let W := ∏ i ∈ s, (1 + g i)
    let A := ∑ i ∈ s, (g i / (1 + g i)) * f i
    let v : Finset ι → ℝ := fun t => ∏ i ∈ t, g i
    let L : Finset ι → ℝ := fun t => ∑ i ∈ t, f i
    change (∑ t ∈ (insert a s).powerset, v t * L t) = _
    have hins : ∑ t ∈ s.powerset, v (insert a t) * L (insert a t) =
        g a * (f a * W + W * A) := by
      calc
        _ = ∑ t ∈ s.powerset, g a * (f a * v t + v t * L t) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have hat : a ∉ t := fun h => ha (Finset.mem_powerset.mp ht h)
          dsimp only [v, L]
          rw [Finset.prod_insert hat, Finset.sum_insert hat]
          ring
        _ = _ := by
          change ∑ t ∈ s.powerset, g a * (f a * (∏ i ∈ t, g i) +
            (∏ i ∈ t, g i) * ∑ i ∈ t, f i) = _
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ih hs]
          rw [← Finset.prod_one_add]
    rw [Finset.sum_powerset_insert ha, hins]
    change (∑ t ∈ s.powerset, (∏ i ∈ t, g i) * ∑ i ∈ t, f i) + _ = _
    rw [ih hs, Finset.prod_insert ha, Finset.sum_insert ha]
    change W * A + g a * (f a * W + W * A) = (1 + g a) * W * (g a / (1 + g a) * f a + A)
    field_simp
    ring

/-- The mass of the subsets whose weight sum exceeds `T` is bounded by the
first moment divided by `T`. -/
theorem subset_product_truncation {ι : Type*} (s : Finset ι) (g f : ι → ℝ) {T : ℝ}
    (hg : ∀ i ∈ s, 0 ≤ g i) (hf : ∀ i ∈ s, 0 ≤ f i) (hT : 0 < T)
    (hmean : (∑ i ∈ s, (g i / (1 + g i)) * f i) ≤ T / 2) :
    (∏ i ∈ s, (1 + g i)) / 2 ≤
      ∑ t ∈ s.powerset.filter (fun t : Finset ι => (∑ i ∈ t, f i) ≤ T), ∏ i ∈ t, g i := by
  classical
  let v : Finset ι → ℝ := fun t => ∏ i ∈ t, g i
  let L : Finset ι → ℝ := fun t => ∑ i ∈ t, f i
  let W := ∏ i ∈ s, (1 + g i)
  let lo := s.powerset.filter (fun t : Finset ι => L t ≤ T)
  let hi := s.powerset.filter (fun t : Finset ι => ¬ L t ≤ T)
  have hv : ∀ t ∈ s.powerset, 0 ≤ v t := fun t ht =>
    Finset.prod_nonneg fun i hi => hg i (Finset.mem_powerset.mp ht hi)
  have hL : ∀ t ∈ s.powerset, 0 ≤ L t := fun t ht =>
    Finset.sum_nonneg fun i hi => hf i (Finset.mem_powerset.mp ht hi)
  have hW : 0 ≤ W := Finset.prod_nonneg fun i hi => by linarith [hg i hi]
  have hsplit : (∑ t ∈ lo, v t) + ∑ t ∈ hi, v t = W := by
    dsimp [lo, hi, W, v]
    rw [Finset.sum_filter_add_sum_filter_not, ← Finset.prod_one_add]
  have hhi : hi ⊆ s.powerset := Finset.filter_subset ..
  have hupper : T * (∑ t ∈ hi, v t) ≤ W * (T / 2) := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ t ∈ hi, v t * L t := by
        refine Finset.sum_le_sum fun t ht => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp ht).2))
          (hv t (hhi ht))
      _ ≤ ∑ t ∈ s.powerset, v t * L t :=
        Finset.sum_le_sum_of_subset_of_nonneg hhi (fun t ht _ => mul_nonneg (hv t ht) (hL t ht))
      _ = W * (∑ i ∈ s, (g i / (1 + g i)) * f i) := subset_product_first_moment s g f hg
      _ ≤ W * (T / 2) := mul_le_mul_of_nonneg_left hmean hW
  have hthird : (∑ t ∈ hi, v t) ≤ W / 2 := by
    apply le_of_mul_le_mul_left _ hT
    calc T * (∑ t ∈ hi, v t) ≤ W * (T / 2) := hupper
      _ = T * (W / 2) := by ring
  change W / 2 ≤ ∑ t ∈ lo, v t
  linarith only [hsplit, hthird]

/-- At a dyadic cutoff, Chebyshev bounds the logarithmic mean of the sieve factors. -/
theorem sum_prime_log_div_dyadic (k : ℕ) :
    (∑ p ∈ Nat.primesLE (2^k), Real.log (p : ℝ) / (p : ℝ)) ≤
      2 * Real.log 4 * (k : ℝ) := by
  induction k with
  | zero => simp [Nat.primesLE_one]
  | succ k ih =>
    let z : ℕ := 2^k
    let w : ℕ := 2^(k+1)
    have hzw : z ≤ w := Nat.pow_le_pow_right (by decide) (Nat.le_succ k)
    have hz : 0 < z := by dsimp [z]; positivity
    have hz' : (0 : ℝ) < z := Nat.cast_pos.mpr hz
    have hw : (w : ℝ) = 2 * (z : ℝ) := by
      dsimp [w, z]
      push_cast
      ring
    let P := Nat.primesLE z
    let Q := Nat.primesLE w
    have hPQ : P ⊆ Q := Nat.primesLE_mono hzw
    have htail : (∑ p ∈ Q \ P, Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * Real.log 4 := by
      calc
        _ ≤ ∑ p ∈ Q \ P, Real.log (p : ℝ) / (z : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hmem := Finset.mem_sdiff.mp hp
          have hpP := Nat.prime_of_mem_primesLE hmem.1
          have hp_ge : z ≤ p := le_of_lt (lt_of_not_ge (fun h =>
            hmem.2 (Nat.mem_primesLE.mpr ⟨h, hpP⟩)))
          exact div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast hpP.one_le))
            hz' (by exact_mod_cast hp_ge)
        _ ≤ ∑ p ∈ Q, Real.log (p : ℝ) / (z : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun p hp _ => ?_
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
            hz'.le
        _ = Chebyshev.theta (w : ℝ) / (z : ℝ) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.sum_div]
        _ ≤ (Real.log 4 * (w : ℝ)) / (z : ℝ) :=
          div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) hz'.le
        _ = _ := by rw [hw]; field_simp
    change (∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ)) ≤ _
    rw [← Finset.sum_sdiff hPQ]
    push_cast
    change _ ≤ 2 * Real.log 4 * ((k : ℝ) + 1)
    change (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤ 2 * Real.log 4 * (k : ℝ) at ih
    linarith only [ih, htail]

end FareyGoldbach
