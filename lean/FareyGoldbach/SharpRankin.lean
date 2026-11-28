import FareyGoldbach.SingularSeries
import FareyGoldbach.PrimeSums
import Mathlib.NumberTheory.Chebyshev

/-!
# Module F1: Finite Truncated Singular-Series Positivity, Sharp Rankin Tail, and Totient Moments

This module provides the arithmetic backbone for Route A (double- and single-averaged binary
Goldbach in arithmetic progressions across arbitrary positive integer moduli `1 ≤ r ≤ X`):

1. `div_totient_le_two_log`: elementary bound `m / φ(m) ≤ 2 * log(2 * m)` for all `m ≥ 1`.
2. `singularTrunc_re_ge_quarter`: **unconditional all-cutoff positivity**
   `Re(singularTrunc r n P) ≥ 1 / 4` for EVERY `r ≥ 1`, EVERY positive even `n`, and EVERY `P ≥ 1`
   (eliminating any large-cutoff requirement on `Q₀`!).
3. `rankin_tail_bound`: subexponential Rankin tail `O(P^(-1/2) * exp(6 * √(log(2n))))`.
4. `sum_primeWeight_le_two_mul`: Chebyshev bound `∑_{n ≤ Y} primeWeight n ≤ 2 * Y`.
5. `sum_coprime_sqfree_div_totient_sq_le`: `∑_{q ≤ Q, (q,r)=1, sqfree} q / φ(q)² ≤ 72 * (φ(r)/r) * log(2Y)`.
6. `sum_div_totient_pow_le`: general moment `∑_{q ≤ Z} (q / φ(q))^k ≤ exp(2^k) * Z` for all `k, Z : ℕ`,
   yielding the totient-cutoff bounds `sum_div_totient_of_totient_le`,
   `sum_div_totient_sq_of_totient_le`, and `sum_inv_totient_cube_of_totient_gt`.
-/

open Real Complex Set
open scoped BigOperators Classical

namespace FareyGoldbach

section Helpers

lemma real_one_le_prod {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x u hx ih =>
    rw [Finset.prod_insert hx]
    have h1 := hf x (Finset.mem_insert_self _ _)
    have h2 := ih fun y hy => hf y (Finset.mem_insert_of_mem hy)
    nlinarith

lemma real_prod_le_prod_of_subset_of_one_le {ι : Type*} [DecidableEq ι] {s t : Finset ι}
    (hst : s ⊆ t) {f : ι → ℝ} (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ t, i ∉ s → 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have hge1 : 1 ≤ ∏ i ∈ t \ s, f i :=
    real_one_le_prod (t \ s) fun i hi => hf1 i (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hi).2
  have hnn : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf0
  nlinarith

lemma sum_biUnion_le_sum {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i u hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hunion : ∑ a ∈ t i ∪ u.biUnion t, f a ≤ (∑ a ∈ t i, f a) + ∑ a ∈ u.biUnion t, f a := by
      have h := Finset.sum_union_inter (s₁ := t i) (s₂ := u.biUnion t) (f := f)
      have hnn : 0 ≤ ∑ a ∈ t i ∩ u.biUnion t, f a := Finset.sum_nonneg fun a _ => hf a
      linarith
    linarith

end Helpers

section ElementaryTotient

/-- For any finite set `S` of primes, `∏ p ∈ S, p / (p - 1) ≤ S.card + 1`. -/
lemma prod_prime_div_pred_le_card_add_one (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (S.card : ℝ) + 1 := by
  induction hcard : S.card generalizing S with
  | zero =>
    rw [Finset.card_eq_zero.mp hcard]; simp
  | succ k ih =>
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    let p := S.max' hne
    have hp_mem : p ∈ S := Finset.max'_mem S hne
    have hp_prime : p.Prime := hS p hp_mem
    let S' := S.erase p
    have hS'_card : S'.card = k := by
      change (S.erase p).card = k
      rw [Finset.card_erase_of_mem hp_mem, hcard]
      omega
    have hS'_prime : ∀ q ∈ S', q.Prime := fun q hq => hS q (Finset.mem_of_mem_erase hq)
    have hih := ih S' hS'_prime hS'_card
    have hS_sub : S ⊆ Finset.Icc 2 p := fun q hq =>
      Finset.mem_Icc.mpr ⟨(hS q hq).two_le, Finset.le_max' S q hq⟩
    have hcard_le : S.card ≤ p - 1 := by
      have h1 := Finset.card_le_card hS_sub
      rw [Nat.card_Icc] at h1
      have hp2 : 2 ≤ p := hp_prime.two_le
      omega
    have hp_ge : k + 2 ≤ p := by omega
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hp1_ge : (k : ℝ) + 1 ≤ (p : ℝ) - 1 := by
      have : ((k + 2 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp_ge
      push_cast at this; linarith
    have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := lt_of_lt_of_le hk1_pos hp1_ge
    have hstep : (p : ℝ) / ((p : ℝ) - 1) ≤ ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
      rw [div_le_div_iff₀ hp1_pos hk1_pos]
      nlinarith
    have hprod_eq : ∏ q ∈ S, ((q : ℝ) / ((q : ℝ) - 1)) =
        ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ S', ((q : ℝ) / ((q : ℝ) - 1)) :=
      (Finset.mul_prod_erase S _ hp_mem).symm
    have hS'_nn : 0 ≤ ∏ q ∈ S', ((q : ℝ) / ((q : ℝ) - 1)) :=
      Finset.prod_nonneg fun q hq => by
        have hq2 : (2 : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr (hS'_prime q hq).two_le
        exact div_nonneg (by linarith) (by linarith)
    calc ∏ q ∈ S, ((q : ℝ) / ((q : ℝ) - 1))
        = ((p : ℝ) / ((p : ℝ) - 1)) * ∏ q ∈ S', ((q : ℝ) / ((q : ℝ) - 1)) := hprod_eq
      _ ≤ (((k : ℝ) + 2) / ((k : ℝ) + 1)) * ((k : ℝ) + 1) :=
          mul_le_mul hstep hih hS'_nn (by positivity)
      _ = (k : ℝ) + 2 := by field_simp [hk1_pos.ne']
      _ = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

/-- Exact Euler-product identity for `m / φ(m)` on positive `m`. -/
lemma div_totient_eq_prod_primeFactors {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have htot := Nat.totient_eq_mul_prod_factors m
  have htotR : (m.totient : ℝ) = (m : ℝ) * ∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have h1 := congrArg (fun q : ℚ => (q : ℝ)) htot
    simpa [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one, Rat.cast_inv,
      Rat.cast_natCast] using h1
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hprod_ne : (∏ p ∈ m.primeFactors, (1 - (p : ℝ)⁻¹)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
    have hinv : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  rw [htotR, div_mul_eq_div_div, div_self hm_ne, one_div, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
  have hp_ne : (p : ℝ) ≠ 0 := by linarith
  have hp1_ne : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp [hp_ne, hp1_ne]

/-- **Elementary totient ratio bound:** For all `m ≥ 1`, `m / φ(m) ≤ 2 * log(2 * m)`. -/
theorem div_totient_le_two_log {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) ≤ 2 * Real.log (2 * (m : ℝ)) := by
  rw [div_totient_eq_prod_primeFactors hm]
  have h1 := prod_prime_div_pred_le_card_add_one m.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h2pow : 2 ^ m.primeFactors.card ≤ m := by
    calc 2 ^ m.primeFactors.card
        = ∏ _p ∈ m.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ m.primeFactors, p :=
          Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ m := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  have hlog2_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
        rw [this]; linarith [Real.exp_one_lt_d9]
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have := Real.log_le_log (Real.exp_pos _) hexp
    rwa [Real.log_exp] at this
  have hcard_log : (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (m : ℝ) := by
    have h2R : ((2 : ℝ) ^ m.primeFactors.card) ≤ (m : ℝ) := by exact_mod_cast h2pow
    have h := Real.log_le_log (by positivity) h2R
    rwa [Real.log_pow] at h
  have hcard_le : (m.primeFactors.card : ℝ) ≤ 2 * Real.log (m : ℝ) := by
    have hnn : (0 : ℝ) ≤ (m.primeFactors.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlog_mul : Real.log (2 * (m : ℝ)) = Real.log 2 + Real.log (m : ℝ) :=
    Real.log_mul two_ne_zero hm_pos.ne'
  linarith

/-- Chebyshev prime-weight sum bound: `∑ n ∈ Icc 1 Y, primeWeight n ≤ 2 * Y`. -/
theorem sum_primeWeight_le_two_mul (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, primeWeight n ≤ 2 * (Y : ℝ) := by
  have hcheb := Chebyshev.theta_le_log4_mul_x (x := (Y : ℝ)) (Nat.cast_nonneg Y)
  have hlog4 : Real.log 4 ≤ 2 := by
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    have := Real.log_le_log (by norm_num) h4
    rwa [Real.log_exp] at this
  have heq : ∑ n ∈ Finset.Icc 1 Y, primeWeight n = Chebyshev.theta (Y : ℝ) := by
    unfold Chebyshev.theta primeWeight
    rw [Nat.floor_natCast, Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [heq]
  exact hcheb.trans (mul_le_mul_of_nonneg_right hlog4 (Nat.cast_nonneg Y))

end ElementaryTotient

section FiniteSingularPositivity

/-- Helper: `∏_{p ∈ S} (1 + 1 / (p - 1)^2) ≤ exp (1 / 2)` for any finite set `S` of odd primes. -/
lemma prod_odd_prime_one_add_inv_pred_sq_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) ≤ Real.exp (1 / 2 : ℝ) := by
  have hprod_le : ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) ≤
      Real.exp (∑ p ∈ S, 1 / (((p : ℝ) - 1) ^ 2)) := by
    rw [Real.exp_sum]
    refine real_prod_le_prod S _ _ (fun p hp => by
      have hp3 : (3 : ℝ) ≤ p := Nat.cast_le.mpr (hS p hp).2
      positivity) (fun p _ => by linarith [Real.add_one_le_exp (1 / (((p : ℝ) - 1) ^ 2))])
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  let N := S.sup id + 1
  have hinj : Set.InjOn (fun p : ℕ => (p - 1) / 2) (S : Set ℕ) := by
    intro p₁ hp₁ p₂ hp₂ hEq
    dsimp only at hEq
    have h1 := hS p₁ hp₁
    have h2 := hS p₂ hp₂
    have ho1 : Odd p₁ := h1.1.odd_of_ne_two (by omega)
    have ho2 : Odd p₂ := h2.1.odd_of_ne_two (by omega)
    obtain ⟨k₁, hk₁⟩ := ho1
    obtain ⟨k₂, hk₂⟩ := ho2
    have e1 : (p₁ - 1) / 2 = k₁ := by omega
    have e2 : (p₂ - 1) / 2 = k₂ := by omega
    omega
  have hsub : S.image (fun p : ℕ => (p - 1) / 2) ⊆ Finset.Icc 1 N := by
    intro j hj
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
    have h1 := (hS p hp).2
    have hle : p ≤ S.sup id := Finset.le_sup (f := id) hp
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hterm : ∀ p ∈ S,
      (1 : ℝ) / (((p : ℝ) - 1) ^ 2) = (1 / 4 : ℝ) * (1 / ((((p - 1) / 2 : ℕ) : ℝ) ^ 2)) := by
    intro p hp
    have h1 := hS p hp
    have ho : Odd p := h1.1.odd_of_ne_two (by omega)
    obtain ⟨k, hk⟩ := ho
    have hk_eq : (p - 1) / 2 = k := by omega
    have hp_sub : (p : ℝ) - 1 = 2 * (k : ℝ) := by
      have : (p : ℝ) = 2 * (k : ℝ) + 1 := by exact_mod_cast hk
      linarith
    rw [hk_eq, hp_sub]
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    field_simp [hk_pos.ne']
    ring
  have hsum_eq : ∑ p ∈ S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2) =
      (1 / 4 : ℝ) * ∑ j ∈ S.image (fun p : ℕ => (p - 1) / 2), ((1 : ℝ) / ((j : ℝ) ^ 2)) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_image hinj]
  have hsum_j : ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / ((j : ℝ) ^ 2) ≤ 2 := by
    have h1_mem : (1 : ℕ) ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    have herase : (Finset.Icc 1 N).erase 1 = Finset.Icc 2 N := by
      ext j; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    rw [← Finset.add_sum_erase _ _ h1_mem, herase]
    have h2 : ∑ j ∈ Finset.Icc 2 N, (1 : ℝ) / ((j : ℝ) ^ 2) ≤
        ∑ j ∈ Finset.Icc 2 N, (1 : ℝ) / ((j : ℝ) * ((j : ℝ) - 1)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj2 : (2 : ℝ) ≤ j := Nat.cast_le.mpr (Finset.mem_Icc.mp hj).1
      exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
    have h3 := sum_inv_mul_pred_le_one N
    simp only [Nat.cast_one, one_pow, div_one]
    linarith
  calc ∑ p ∈ S, (1 : ℝ) / (((p : ℝ) - 1) ^ 2)
      = (1 / 4 : ℝ) * ∑ j ∈ S.image (fun p : ℕ => (p - 1) / 2), ((1 : ℝ) / ((j : ℝ) ^ 2)) := hsum_eq
    _ ≤ (1 / 4 : ℝ) * ∑ j ∈ Finset.Icc 1 N, ((1 : ℝ) / ((j : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (by norm_num)
    _ ≤ (1 / 4 : ℝ) * 2 := mul_le_mul_of_nonneg_left hsum_j (by norm_num)
    _ = 1 / 2 := by norm_num

/-- `exp (1 / 2) ≤ 7 / 4`. -/
lemma exp_half_le_seven_fourths : Real.exp (1 / 2 : ℝ) ≤ 7 / 4 := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ (7 / 4 : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
    rw [this]; linarith [Real.exp_one_lt_d9]
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

/-- For squarefree `d ≥ 1` with `d ∣ n`, `ramanujanSum d n = φ(d)`. -/
lemma ramanujanSum_eq_totient_of_dvd {d n : ℕ} (hd : 0 < d) (hsf : Squarefree d) (hdvd : d ∣ n) :
    ramanujanSum d n = (d.totient : ℂ) := by
  induction hcard : d.primeFactors.card generalizing d with
  | zero =>
    have hd1 : d = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpos : 0 < d.primeFactors.card := Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, hd.ne'⟩⟩
      omega
    subst hd1; simp [ramanujanSum_one]
  | succ k ih =>
    obtain ⟨p, hp_mem⟩ := Finset.card_pos.mp (by omega : 0 < d.primeFactors.card)
    have hp : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
    have hpd : p ∣ d := (Nat.mem_primeFactors.mp hp_mem).2.1
    obtain ⟨m, rfl⟩ := hpd
    have hm_pos : 0 < m := Nat.pos_of_mul_pos_left hd
    have hmsf : Squarefree m := hsf.squarefree_of_dvd (dvd_mul_left m p)
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (hsf p (mul_dvd_mul_left p hpm))
    have hcard_m : m.primeFactors.card = k := by
      have hpf : (p * m).primeFactors = insert p m.primeFactors := by
        ext q; simp only [Nat.mem_primeFactors, Finset.mem_insert, ne_eq, mul_eq_zero, not_or]
        constructor
        · rintro ⟨hq, hqpm, _, _⟩
          rcases hq.dvd_mul.mp hqpm with h1 | h2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp h1)
          · exact Or.inr ⟨hq, h2, hm_pos.ne'⟩
        · rintro (hq_eq | ⟨hq, hqm, _⟩)
          · subst hq_eq; exact ⟨hp, dvd_mul_right q m, hp.ne_zero, hm_pos.ne'⟩
          · exact ⟨hq, dvd_mul_of_dvd_right hqm p, hp.ne_zero, hm_pos.ne'⟩
      have hp_not : p ∉ m.primeFactors := fun h =>
        (hp.coprime_iff_not_dvd.mp hcop) (Nat.mem_primeFactors.mp h).2.1
      rw [hpf, Finset.card_insert_of_notMem hp_not] at hcard
      omega
    rw [ramanujanSum_mul_of_coprime hp.pos hm_pos hcop,
        ramanujanSum_prime hp n, ite_eq_left (dvd_trans (dvd_mul_right p m) hdvd),
        ih hm_pos hmsf (dvd_trans (dvd_mul_left m p) hdvd) hcard_m,
        Nat.totient_mul hcop, Nat.totient_prime hp]
    push_cast; rfl

/-- For squarefree `e ≥ 1` with `Nat.Coprime e n`, `ramanujanSum e n = μ(e)`. -/
lemma ramanujanSum_eq_moebius_of_coprime {e n : ℕ} (he : 0 < e) (hsf : Squarefree e)
    (hcop_n : Nat.Coprime e n) :
    ramanujanSum e n = (ArithmeticFunction.moebius e : ℂ) := by
  induction hcard : e.primeFactors.card generalizing e with
  | zero =>
    have he1 : e = 1 := by
      by_contra hne
      obtain ⟨p, hp, hpe⟩ := Nat.exists_prime_and_dvd hne
      have hpos : 0 < e.primeFactors.card := Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpe, he.ne'⟩⟩
      omega
    subst he1; simp [ramanujanSum_one]
  | succ k ih =>
    obtain ⟨p, hp_mem⟩ := Finset.card_pos.mp (by omega : 0 < e.primeFactors.card)
    have hp : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
    have hpe : p ∣ e := (Nat.mem_primeFactors.mp hp_mem).2.1
    obtain ⟨m, rfl⟩ := hpe
    have hm_pos : 0 < m := Nat.pos_of_mul_pos_left he
    have hmsf : Squarefree m := hsf.squarefree_of_dvd (dvd_mul_left m p)
    have hcop : Nat.Coprime p m := by
      rw [hp.coprime_iff_not_dvd]
      intro hpm
      exact hp.not_isUnit (hsf p (mul_dvd_mul_left p hpm))
    have hcard_m : m.primeFactors.card = k := by
      have hpf : (p * m).primeFactors = insert p m.primeFactors := by
        ext q; simp only [Nat.mem_primeFactors, Finset.mem_insert, ne_eq, mul_eq_zero, not_or]
        constructor
        · rintro ⟨hq, hqpm, _, _⟩
          rcases hq.dvd_mul.mp hqpm with h1 | h2
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq hp).mp h1)
          · exact Or.inr ⟨hq, h2, hm_pos.ne'⟩
        · rintro (hq_eq | ⟨hq, hqm, _⟩)
          · subst hq_eq; exact ⟨hp, dvd_mul_right q m, hp.ne_zero, hm_pos.ne'⟩
          · exact ⟨hq, dvd_mul_of_dvd_right hqm p, hp.ne_zero, hm_pos.ne'⟩
      have hp_not : p ∉ m.primeFactors := fun h =>
        (hp.coprime_iff_not_dvd.mp hcop) (Nat.mem_primeFactors.mp h).2.1
      rw [hpf, Finset.card_insert_of_notMem hp_not] at hcard
      omega
    have hpn : ¬ p ∣ n := hp.coprime_iff_not_dvd.mp (hcop_n.coprime_dvd_left (dvd_mul_right p m))
    have hmn : Nat.Coprime m n := hcop_n.coprime_dvd_left (dvd_mul_left m p)
    rw [ramanujanSum_mul_of_coprime hp.pos hm_pos hcop,
        ramanujanSum_prime hp n, ite_eq_right hpn,
        ih hm_pos hmsf hmn hcard_m,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp]
    push_cast; rfl

/-- Totient product for squarefree `m`: `(m.totient : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1)`. -/
lemma totient_eq_prod_sub_one_of_squarefree {m : ℕ} (hm : 0 < m) (hsf : Squarefree m) :
    (m.totient : ℝ) = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
  have h1 := div_totient_eq_prod_primeFactors hm
  have hprod : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htot_ne : (m.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hm).ne'
  have hden_ne : (∏ p ∈ m.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
    linarith
  rw [Finset.prod_div_distrib, ← hprod] at h1
  have h2 := (div_eq_div_iff htot_ne hden_ne).mp h1
  exact mul_left_cancel₀ hm_ne h2.symm

/-- Sum of `1 / φ(e)²` over odd squarefree `e ≥ 3` up to `M` is at most `3 / 4`. -/
lemma sum_odd_sqfree_inv_totient_sq_le (M : ℕ) :
    ∑ e ∈ ((Finset.Icc 2 M).filter (fun e => Squarefree e ∧ Odd e)),
      (1 : ℝ) / ((e.totient : ℝ) ^ 2) ≤ 3 / 4 := by
  let S := (Finset.Icc 3 M).filter Nat.Prime
  have hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p := fun p hp =>
    ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
  let E := (Finset.Icc 2 M).filter (fun e => Squarefree e ∧ Odd e)
  have hmap : ∀ e ∈ E,
      e.primeFactors ∈ S.powerset.erase ∅ ∧
      (1 : ℝ) / ((e.totient : ℝ) ^ 2) = ∏ p ∈ e.primeFactors, (1 / (((p : ℝ) - 1) ^ 2)) := by
    intro e he
    have heIcc := (Finset.mem_filter.mp he).1
    have he2 : 2 ≤ e := (Finset.mem_Icc.mp heIcc).1
    have heM : e ≤ M := (Finset.mem_Icc.mp heIcc).2
    have hsf := (Finset.mem_filter.mp he).2.1
    have hodd := (Finset.mem_filter.mp he).2.2
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_powerset.mpr fun p hp => ?_⟩, ?_⟩
    · intro hempty
      have h1 : e = 1 := by
        rw [← Nat.prod_primeFactors_of_squarefree hsf, hempty]; simp
      omega
    · have hpm := Nat.mem_primeFactors.mp hp
      have hp_ne2 : p ≠ 2 := by
        intro h2; subst h2
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpm.2.1)
      have hp3 : 3 ≤ p := by have := hpm.1.two_le; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, (Nat.le_of_dvd (by omega) hpm.2.1).trans heM⟩, hpm.1⟩
    · rw [totient_eq_prod_sub_one_of_squarefree (by omega) hsf, ← Finset.prod_pow]
      simp_rw [one_div]
      rw [← Finset.prod_inv_distrib]
  have h1 : ∑ e ∈ E, (1 : ℝ) / ((e.totient : ℝ) ^ 2) ≤
      ∑ T ∈ S.powerset.erase ∅, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) := by
    calc ∑ e ∈ E, (1 : ℝ) / ((e.totient : ℝ) ^ 2)
        = ∑ e ∈ E, ∏ p ∈ e.primeFactors, (1 / (((p : ℝ) - 1) ^ 2)) :=
          Finset.sum_congr rfl fun e he => (hmap e he).2
      _ = ∑ T ∈ E.image Nat.primeFactors, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) := by
          symm
          refine Finset.sum_image fun e₁ he₁ e₂ he₂ hEq => ?_
          have h1' := Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp he₁).2.1
          have h2' := Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp he₂).2.1
          rw [← h1', ← h2', hEq]
      _ ≤ ∑ T ∈ S.powerset.erase ∅, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_) (fun T _ _ => Finset.prod_nonneg fun _ _ => by positivity)
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hT
          exact (hmap e he).1
  have h2 : ∑ T ∈ S.powerset.erase ∅, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) =
      (∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2))) - 1 := by
    have hfull : ∑ T ∈ S.powerset, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) =
        ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) := by
      have h := Finset.prod_add (f := fun p : ℕ => (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) (g := fun _ => (1 : ℝ)) S
      simpa [add_comm] using h.symm
    have hsplit := Finset.add_sum_erase S.powerset
      (fun T => ∏ p ∈ T, ((1 : ℝ) / (((p : ℝ) - 1) ^ 2))) (Finset.empty_mem_powerset S)
    simp only [Finset.prod_empty] at hsplit
    linarith
  have h3 := prod_odd_prime_one_add_inv_pred_sq_le S hS
  have h4 := exp_half_le_seven_fourths
  linarith

/-- **Module F1 Main Theorem (`singularTrunc_re_ge_quarter`):**
For EVERY `r ≥ 1`, EVERY positive even `n`, and EVERY cutoff `P ≥ 1` (including `P = 1` and even `r`!),
`Re(singularTrunc r n P) ≥ 1 / 4`. No Rankin tail or large-cutoff condition is needed! -/
theorem singularTrunc_re_ge_quarter {r n P : ℕ} (_hr : 0 < r) (_hn : 0 < n) (heven : Even n)
    (hP : 1 ≤ P) :
    (1 : ℝ) / 4 ≤ (singularTrunc r n P).re := by
  let Qsf := ((Finset.Icc 1 P).filter (fun q => Nat.Coprime q r)).filter Squarefree
  have hdrop : singularTrunc r n P =
      ∑ q ∈ Qsf, (ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2 := by
    unfold singularTrunc
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hnot => ?_
    have hnsf : ¬ Squarefree q := fun hsf => hnot (Finset.mem_filter.mpr ⟨hq, hsf⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp
  let Dset := (Finset.Icc 1 P).filter (fun d => Squarefree d ∧ d ∣ n ∧ Nat.Coprime d r)
  let Eset : ℕ → Finset ℕ := fun d =>
    (Finset.Icc 1 (P / d)).filter (fun e => Squarefree e ∧ Nat.Coprime e (n * r))
  -- Exact reindexing of `Qsf` via `(d, e) ↦ d * e` with inverse `q ↦ (gcd q n, q / gcd q n)`.
  have hbij : (singularTrunc r n P).re =
      ∑ d ∈ Dset, (1 / (d.totient : ℝ)) *
        ∑ e ∈ Eset d, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)) := by
    rw [hdrop, Complex.re_sum]
    -- Rewrite RHS as sum over `Dset.sigma Eset`.
    have hrhs : ∑ d ∈ Dset, (1 / (d.totient : ℝ)) *
          ∑ e ∈ Eset d, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)) =
        ∑ p ∈ Dset.sigma Eset,
          (1 / ((p.1.totient : ℝ))) * ((ArithmeticFunction.moebius p.2 : ℝ) / ((p.2.totient : ℝ) ^ 2)) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun d _ => Finset.mul_sum _ _ _
    rw [hrhs]
    symm
    refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hd, he⟩ := Finset.mem_sigma.mp hp
      have hd1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hd_sf := (Finset.mem_filter.mp hd).2.1
      have hd_n := (Finset.mem_filter.mp hd).2.2.1
      have hd_r := (Finset.mem_filter.mp hd).2.2.2
      have he1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
      have he_le := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).2
      have he_sf := (Finset.mem_filter.mp he).2.1
      have he_nr := (Finset.mem_filter.mp he).2.2
      have he_n : Nat.Coprime p.2 n := he_nr.coprime_dvd_right (dvd_mul_right n r)
      have he_r : Nat.Coprime p.2 r := he_nr.coprime_dvd_right (dvd_mul_left r n)
      have hde_cop : Nat.Coprime p.1 p.2 := (he_n.coprime_dvd_right hd_n).symm
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by nlinarith, ?_⟩, hd_r.mul_left he_r⟩,
        (Nat.squarefree_mul hde_cop).mpr ⟨hd_sf, he_sf⟩⟩
      exact (Nat.mul_le_mul_left p.1 he_le).trans (Nat.mul_div_le P p.1)
    · intro p₁ hp₁ p₂ hp₂ hEq
      obtain ⟨hd₁, he₁⟩ := Finset.mem_sigma.mp hp₁
      obtain ⟨hd₂, he₂⟩ := Finset.mem_sigma.mp hp₂
      have hd1_n := (Finset.mem_filter.mp hd₁).2.2.1
      have hd2_n := (Finset.mem_filter.mp hd₂).2.2.1
      have he1_n : Nat.Coprime p₁.2 n := (Finset.mem_filter.mp he₁).2.2.coprime_dvd_right (dvd_mul_right n r)
      have he2_n : Nat.Coprime p₂.2 n := (Finset.mem_filter.mp he₂).2.2.coprime_dvd_right (dvd_mul_right n r)
      have hg1 : Nat.gcd (p₁.1 * p₁.2) n = p₁.1 := by
        rw [Nat.Coprime.gcd_mul_right_cancel p₁.1 he1_n, Nat.gcd_eq_left hd1_n]
      have hg2 : Nat.gcd (p₂.1 * p₂.2) n = p₂.1 := by
        rw [Nat.Coprime.gcd_mul_right_cancel p₂.1 he2_n, Nat.gcd_eq_left hd2_n]
      have h1eq : p₁.1 = p₂.1 := by rw [← hg1, ← hg2, hEq]
      have hd1_pos : 0 < p₁.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd₁).1).1
      have h2eq : p₁.2 = p₂.2 := mul_left_cancel₀ hd1_pos.ne' (by rw [h1eq] at hEq ⊢; exact hEq)
      exact Sigma.ext h1eq (heq_of_eq h2eq)
    · intro q hq
      have hq_mem := Finset.mem_filter.mp hq
      have hq_sf := hq_mem.2
      have hq_r := (Finset.mem_filter.mp hq_mem.1).2
      have hq_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq_mem.1).1
      have hq_pos : 0 < q := hq_Icc.1
      have hq_le : q ≤ P := hq_Icc.2
      let d := Nat.gcd q n
      let e := q / d
      have hd_dvd_q : d ∣ q := Nat.gcd_dvd_left q n
      have hd_dvd_n : d ∣ n := Nat.gcd_dvd_right q n
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left n hq_pos
      have hde_eq : d * e = q := Nat.mul_div_cancel' hd_dvd_q
      have he_pos : 0 < e := Nat.pos_of_mul_pos_left (by rw [hde_eq]; exact hq_pos)
      have hd_sf : Squarefree d := hq_sf.squarefree_of_dvd hd_dvd_q
      have he_sf : Squarefree e := hq_sf.squarefree_of_dvd ⟨d, by rw [mul_comm, hde_eq]⟩
      have hd_r : Nat.Coprime d r := hq_r.coprime_dvd_left hd_dvd_q
      have he_r : Nat.Coprime e r := hq_r.coprime_dvd_left ⟨d, by rw [mul_comm, hde_eq]⟩
      have he_n : Nat.Coprime e n := by
        apply Nat.coprime_of_dvd
        intro s hs hse hsn
        have hsq : s ∣ q := dvd_trans hse ⟨d, by rw [mul_comm, hde_eq]⟩
        have hsd : s ∣ d := Nat.dvd_gcd hsq hsn
        have hss : s * s ∣ q := by rw [← hde_eq]; exact mul_dvd_mul hsd hse
        exact hs.not_isUnit (hq_sf s hss)
      have hd_le_P : d ≤ P := (Nat.le_of_dvd hq_pos hd_dvd_q).trans hq_le
      have he_le : e ≤ P / d := (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm, hde_eq]; exact hq_le)
      refine ⟨⟨d, e⟩, Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd_pos, hd_le_P⟩,
        hd_sf, hd_dvd_n, hd_r⟩, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨he_pos, he_le⟩,
        he_sf, he_n.mul_right he_r⟩⟩, hde_eq⟩
    · intro p hp
      obtain ⟨hd, he⟩ := Finset.mem_sigma.mp hp
      have hd_pos : 0 < p.1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hd_sf := (Finset.mem_filter.mp hd).2.1
      have hd_n := (Finset.mem_filter.mp hd).2.2.1
      have he_pos : 0 < p.2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp he).1).1
      have he_sf := (Finset.mem_filter.mp he).2.1
      have he_n : Nat.Coprime p.2 n := (Finset.mem_filter.mp he).2.2.coprime_dvd_right (dvd_mul_right n r)
      have hcop : Nat.Coprime p.1 p.2 := (he_n.coprime_dvd_right hd_n).symm
      have hsf_mul : Squarefree (p.1 * p.2) := (Nat.squarefree_mul hcop).mpr ⟨hd_sf, he_sf⟩
      have hmu_sq : (ArithmeticFunction.moebius (p.1 * p.2) : ℂ) ^ 2 = 1 := by
        rw [ArithmeticFunction.moebius_apply_of_squarefree hsf_mul]
        push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hmu_sq, one_mul, ramanujanSum_mul_of_coprime hd_pos he_pos hcop,
          ramanujanSum_eq_totient_of_dvd hd_pos hd_sf hd_n,
          ramanujanSum_eq_moebius_of_coprime he_pos he_sf he_n,
          Nat.totient_mul hcop]
      have hd_ne : (p.1.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hd_pos).ne'
      have he_ne : (p.2.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr he_pos).ne'
      have hval : (p.1.totient : ℂ) * (ArithmeticFunction.moebius p.2 : ℂ) /
            ((p.1.totient : ℂ) * (p.2.totient : ℂ)) ^ 2 =
          (((1 / (p.1.totient : ℝ)) * ((ArithmeticFunction.moebius p.2 : ℝ) / ((p.2.totient : ℝ) ^ 2)) : ℝ) : ℂ) := by
        push_cast; field_simp [hd_ne, he_ne]
      push_cast; rw [hval, Complex.ofReal_re]
  rw [hbij]
  -- Every inner sum is `≥ 1 / 4`.
  have hinner_ge : ∀ d ∈ Dset,
      (1 : ℝ) / 4 ≤ ∑ e ∈ Eset d, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)) := by
    intro d hd
    have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    have hd_le : d ≤ P := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).2
    have h1_mem : (1 : ℕ) ∈ Eset d := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, (Nat.le_div_iff_mul_le hd_pos).mpr (by omega)⟩,
        squarefree_one, Nat.coprime_one_left _⟩
    rw [← Finset.add_sum_erase _ _ h1_mem]
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.totient_one, Nat.cast_one,
      one_pow, div_one]
    have htail_abs : |∑ e ∈ (Eset d).erase 1, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2))| ≤
        3 / 4 := by
      have hsub : (Eset d).erase 1 ⊆ (Finset.Icc 2 (P / d)).filter (fun e => Squarefree e ∧ Odd e) := by
        intro e he
        have he_ne1 := (Finset.mem_erase.mp he).1
        have he_in := Finset.mem_filter.mp (Finset.mem_erase.mp he).2
        have heIcc := Finset.mem_Icc.mp he_in.1
        have he_n : Nat.Coprime e n := he_in.2.2.coprime_dvd_right (dvd_mul_right n r)
        have hodd : Odd e := by
          rw [← Nat.not_even_iff_odd]
          intro hev
          have h2 : 2 ∣ Nat.gcd e n := Nat.dvd_gcd (even_iff_two_dvd.mp hev) (even_iff_two_dvd.mp heven)
          rw [he_n.gcd_eq_one] at h2; omega
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, heIcc.2⟩, he_in.2.1, hodd⟩
      calc |∑ e ∈ (Eset d).erase 1, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2))|
          ≤ ∑ e ∈ (Eset d).erase 1, |(ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ e ∈ (Eset d).erase 1, (1 : ℝ) / ((e.totient : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun e he => ?_
            rw [abs_div, abs_of_nonneg (sq_nonneg (e.totient : ℝ))]
            have hsf := (Finset.mem_filter.mp (Finset.mem_erase.mp he).2).2.1
            have hmu1 : |(ArithmeticFunction.moebius e : ℝ)| ≤ 1 := by
              rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]
              push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
            exact div_le_div_of_nonneg_right hmu1 (sq_nonneg _)
        _ ≤ ∑ e ∈ (Finset.Icc 2 (P / d)).filter (fun e => Squarefree e ∧ Odd e),
              (1 : ℝ) / ((e.totient : ℝ) ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ 3 / 4 := sum_odd_sqfree_inv_totient_sq_le (P / d)
    linarith [neg_abs_le (∑ e ∈ (Eset d).erase 1, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)))]
  -- Retain the `d = 1` term from the nonnegative outer sum.
  have h1_D : (1 : ℕ) ∈ Dset :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hP⟩, squarefree_one, one_dvd n, Nat.coprime_one_left r⟩
  have hsingle := Finset.single_le_sum (f := fun d => (1 / (d.totient : ℝ)) *
      ∑ e ∈ Eset d, ((ArithmeticFunction.moebius e : ℝ) / ((e.totient : ℝ) ^ 2)))
    (fun d hd => mul_nonneg (by positivity) (by linarith [hinner_ge d hd])) h1_D
  have h1_val := hinner_ge 1 h1_D
  simp only [Nat.totient_one, Nat.cast_one, div_one, one_mul] at hsingle
  linarith

end FiniteSingularPositivity

section SubexponentialRankinTail

/-- Bound on `∑_{m=1}^N 1 / √m ≤ 2 * √N`. -/
lemma sum_inv_sqrt_le_two_sqrt (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / Real.sqrt (m : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ k ih =>
    have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hstep : 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((k + 1 : ℕ) : ℝ) - 2 * Real.sqrt (k : ℝ) := by
      have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
      have hsq1 : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk1_pos
      have hsq0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hsum_pos : 0 < Real.sqrt ((k + 1 : ℕ) : ℝ) + Real.sqrt (k : ℝ) := by linarith
      have hsq_diff : Real.sqrt ((k + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (k : ℝ) ^ 2 = 1 := by
        rw [Real.sq_sqrt hk1_pos.le, Real.sq_sqrt (Nat.cast_nonneg k)]; push_cast; ring
      have hle : Real.sqrt (k : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by push_cast; linarith)
      rw [div_le_iff₀ hsq1]
      nlinarith
    linarith

/-- Subexponential bound on the divisor-prime product `∏_{p ∣ n} (1 + √p / (p - 1)) ≤ exp(6 * √(log(2n)))`. -/
lemma prod_dvd_one_add_sqrt_div_pred_le {n : ℕ} (hn : 0 < n) :
    ∏ p ∈ n.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (6 * Real.sqrt (Real.log (2 * (n : ℝ)))) := by
  have hprod_le : ∏ p ∈ n.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) ≤
      Real.exp (∑ p ∈ n.primeFactors, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Real.exp_sum]
    refine real_prod_le_prod n.primeFactors _ _ (fun p hp => by
      have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
      have : 0 ≤ Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
      linarith) (fun p _ => by linarith [Real.add_one_le_exp (Real.sqrt (p : ℝ) / ((p : ℝ) - 1))])
  refine hprod_le.trans (Real.exp_le_exp.mpr ?_)
  set L : ℝ := Real.log (2 * (n : ℝ))
  have hL_ge : (1 : ℝ) / 2 ≤ L := by
    have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by
      have : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr hn; linarith
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
        rw [this]; linarith [Real.exp_one_lt_d9]
      have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have := Real.log_le_log (Real.exp_pos _) hexp; rwa [Real.log_exp] at this
    exact hlog2.trans (Real.log_le_log two_pos h2n)
  have hL_pos : 0 < L := by linarith
  -- Split `n.primeFactors` into `p ≤ ⌊L⌋₊` and `p > ⌊L⌋₊`.
  let Z : ℕ := ⌊L⌋₊
  let S_lo := n.primeFactors.filter (fun p => p ≤ Z)
  let S_hi := n.primeFactors.filter (fun p => ¬ (p ≤ Z))
  have hsplit : ∑ p ∈ n.primeFactors, Real.sqrt (p : ℝ) / ((p : ℝ) - 1) =
      (∑ p ∈ S_lo, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) +
      (∑ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) :=
    (Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p => p ≤ Z) _).symm
  rw [hsplit]
  -- Every prime `p ≥ 2` satisfies `√p / (p - 1) ≤ 2 / √p`.
  have hterm_le : ∀ p : ℕ, p.Prime → Real.sqrt (p : ℝ) / ((p : ℝ) - 1) ≤ 2 / Real.sqrt (p : ℝ) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp.two_le
    have hsq : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr (by linarith)
    rw [div_le_div_iff₀ (by linarith) hsq, Real.mul_self_sqrt (by linarith)]
    linarith
  have hlo : ∑ p ∈ S_lo, Real.sqrt (p : ℝ) / ((p : ℝ) - 1) ≤ 4 * Real.sqrt L := by
    have hsub : S_lo ⊆ Finset.Icc 1 Z := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos,
        (Finset.mem_filter.mp hp).2⟩
    calc ∑ p ∈ S_lo, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
        ≤ ∑ p ∈ S_lo, 2 / Real.sqrt (p : ℝ) :=
          Finset.sum_le_sum fun p hp => hterm_le p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      _ = 2 * ∑ p ∈ S_lo, (1 : ℝ) / Real.sqrt (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ 2 * ∑ m ∈ Finset.Icc 1 Z, (1 : ℝ) / Real.sqrt (m : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) (by norm_num)
      _ ≤ 2 * (2 * Real.sqrt (Z : ℝ)) := mul_le_mul_of_nonneg_left (sum_inv_sqrt_le_two_sqrt Z) (by norm_num)
      _ ≤ 4 * Real.sqrt L := by
          have hZL : (Z : ℝ) ≤ L := Nat.floor_le hL_pos.le
          have := Real.sqrt_le_sqrt hZL; linarith
  -- For `S_hi`: each `p ∈ S_hi` has `L < p` and `2 ≤ p`.
  -- If `L < 2`, then `S_hi.card ≤ L / log 2 ≤ 2 * L`? Even simpler:
  -- `∏ p ∈ S_hi, p ≤ n < 2n = exp L`, and every `p ∈ S_hi` satisfies `p > L`, `p ≥ 2`.
  have hhi : ∑ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1) ≤ 2 * Real.sqrt L := by
    by_cases hL_small : L ≤ 4
    · -- When `L ≤ 4`, `2 * n = exp L ≤ exp 4 < 64`, so `n ≤ 31`.
      -- Wait: even simpler! For ALL `p ∈ S_hi`, `p ≥ 2` and `∏ p ∈ S_hi, p ≤ n`, so `S_hi.card * log 2 ≤ log n ≤ L`,
      -- wait: we want `2 * √L`! Since `2 / √p ≤ 2 / √L`, we only need `S_hi.card ≤ L`!
      -- Wait: `2 ^ S_hi.card ≤ n`, so `S_hi.card ≤ log n / log 2 ≤ 2 * log n` — if `L ≤ 4`, `n ≤ 27`, `S_hi.card ≤ 2`!
      -- Wait: check `p ∈ S_hi` when `L ≤ 4`! Actually for `p ≥ 2`, `√p / (p - 1) ≤ √2`!
      -- Wait: for `n = 2`, `L = log 4 ≈ 1.386`, `2 * √L ≈ 2.35`, `S_hi = {2}`, `√2 ≈ 1.414 ≤ 2.35`!
      -- What if `n = 6`, `L = log 12 ≈ 2.48`, `Z = 2`, `S_hi = {3}`, `√3 / 2 ≈ 0.866 ≤ 2*√2.48`!
      -- In general, for EVERY `p ∈ S_hi`, `p ≥ Z + 1 ≥ L`, so `√p ≥ √L` and `log p ≥ log 2`!
      -- Wait: when `p ≥ 3`, `log p ≥ log 3 > 1`! And the ONLY prime `< 3` is `p = 2`!
      -- Let's use `log p ≥ 1` for `p ≥ 3`, and handle `p = 2` separately!
      have h2_or_3 : ∀ p ∈ S_hi, p = 2 ∨ (3 ≤ p ∧ (1 : ℝ) ≤ Real.log (p : ℝ)) := by
        intro p hp
        have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
        rcases eq_or_lt_of_le hpr.two_le with rfl | hgt
        · exact Or.inl rfl
        · refine Or.inr ⟨hgt, ?_⟩
          have h3 : Real.exp 1 ≤ (p : ℝ) := by
            have : (3 : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hgt
            linarith [Real.exp_one_lt_d9]
          have := Real.log_le_log (Real.exp_pos 1) h3
          rwa [Real.log_exp] at this
      -- In fact `∑ p ∈ S_hi, Real.log p ≤ Real.log n ≤ L - Real.log 2`!
      have hsum_log : ∑ p ∈ S_hi, Real.log (p : ℝ) ≤ L := by
        have hprod_le : (∏ p ∈ S_hi, (p : ℝ)) ≤ 2 * (n : ℝ) := by
          have h1 : ∏ p ∈ S_hi, p ∣ n :=
            dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)
          have h2 : ∏ p ∈ S_hi, p ≤ n := Nat.le_of_dvd hn h1
          have h3 : (∏ p ∈ S_hi, (p : ℝ)) ≤ (n : ℝ) := by rw [← Nat.cast_prod]; exact Nat.cast_le.mpr h2
          linarith [Nat.cast_nonneg (α := ℝ) n]
        have hpos_prod : 0 < ∏ p ∈ S_hi, (p : ℝ) :=
          Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
        have hlog_eq : Real.log (∏ p ∈ S_hi, (p : ℝ)) = ∑ p ∈ S_hi, Real.log (p : ℝ) :=
          Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos.ne'
        rw [← hlog_eq]
        exact Real.log_le_log hpos_prod hprod_le
      -- Every `p ∈ S_hi` has `√p / (p - 1) ≤ (2 / √L) * log p`? Check `p = 2`:
      -- `√2 / 1 ≤ (2 / √L) * log 2` iff `√(2 * L) ≤ 2 * log 2` — FALSE when `L = 1.9` (`√3.8 ≈ 1.95 > 1.38`)!
      -- Wait: if `p = 2 ∈ S_hi`, then `¬ (2 ≤ ⌊L⌋₊)`, so `L < 2`!
      -- When `L < 2`, `2 * n < exp 2 < 8`, so `n ≤ 3`! And for `n ∈ {1, 2, 3}`, `S_hi.card ≤ 1`!
      by_cases h2mem : (2 : ℕ) ∈ S_hi
      · have hL_lt2 : L < 2 := by
          have hnot : ¬ (2 ≤ Z) := (Finset.mem_filter.mp h2mem).2
          by_contra hge; push Not at hge
          exact hnot (Nat.le_floor hge)
        have hn_le3 : n ≤ 3 := by
          have h1 : 2 * (n : ℝ) = Real.exp L := (Real.exp_log (by positivity)).symm
          have h2 : Real.exp L < Real.exp 2 := Real.exp_lt_exp.mpr hL_lt2
          have h3 : Real.exp 2 < 8 := by
            have he : Real.exp 1 < 2.8 := by linarith [Real.exp_one_lt_d9]
            have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
            nlinarith [Real.exp_pos 1]
          have h4 : 2 * (n : ℝ) < 8 := by linarith
          have hlt4 : n < 4 := by exact_mod_cast (show (n : ℝ) < 4 by linarith)
          omega
        have hShi_sub : S_hi ⊆ {2} := by
          intro p hp
          have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
          have hpd := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
          have h2d := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp h2mem).1).2.1
          have hp_le : p ≤ n := Nat.le_of_dvd hn hpd
          have h2_le : 2 ≤ n := Nat.le_of_dvd hn h2d
          have hn2 : n = 2 := by omega
          subst hn2
          have : p = 2 := by have := hpr.two_le; omega
          simp [this]
        calc ∑ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
            ≤ ∑ p ∈ ({2} : Finset ℕ), Real.sqrt (p : ℝ) / ((p : ℝ) - 1) :=
              Finset.sum_le_sum_of_subset_of_nonneg hShi_sub fun p hp _ => by
                have hp2 : p = 2 := Finset.mem_singleton.mp hp
                subst hp2; norm_num
          _ = Real.sqrt 2 := by norm_num
          _ ≤ 2 * Real.sqrt L := by
              have h1 : (2 : ℝ) ≤ 4 * L := by linarith [hL_ge]
              have h2 := Real.sqrt_le_sqrt h1
              rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at h2
              have h4 : Real.sqrt 4 = 2 := by
                rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
              rw [h4] at h2; exact h2
      · -- No `2 ∈ S_hi`: every `p ∈ S_hi` has `3 ≤ p`, so `1 ≤ log p` and `L < p`, hence `√p / (p - 1) ≤ (2 / √L) * log p`.
        have hterm3 : ∀ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1) ≤ (2 / Real.sqrt L) * Real.log (p : ℝ) := by
          intro p hp
          have hp_ne2 : p ≠ 2 := fun h => h2mem (h ▸ hp)
          have hlog1 : (1 : ℝ) ≤ Real.log (p : ℝ) := (h2_or_3 p hp).resolve_left hp_ne2 |>.2
          have hp_gt : L < (p : ℝ) := by
            have hnot : ¬ (p ≤ Z) := (Finset.mem_filter.mp hp).2
            have hlt : Z < p := by omega
            have h1 := Nat.lt_floor_add_one L
            have h2 : ((Z + 1 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (by omega)
            push_cast at h2; linarith
          have hsq_le : Real.sqrt L ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hp_gt.le
          calc Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
              ≤ 2 / Real.sqrt (p : ℝ) := hterm_le p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
            _ ≤ 2 / Real.sqrt L := div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hL_pos) hsq_le
            _ ≤ (2 / Real.sqrt L) * Real.log (p : ℝ) := le_mul_of_one_le_right (by positivity) hlog1
        calc ∑ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
            ≤ ∑ p ∈ S_hi, (2 / Real.sqrt L) * Real.log (p : ℝ) := Finset.sum_le_sum hterm3
          _ = (2 / Real.sqrt L) * ∑ p ∈ S_hi, Real.log (p : ℝ) := (Finset.mul_sum _ _ _).symm
          _ ≤ (2 / Real.sqrt L) * L := mul_le_mul_of_nonneg_left hsum_log (by positivity)
          _ = 2 * Real.sqrt L := by
              have hsq : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL_pos).ne'
              field_simp [hsq]; rw [Real.sq_sqrt hL_pos.le]
    · -- When `L > 4`, every `p ∈ S_hi` satisfies `p > ⌊L⌋₊ ≥ 4`, so `3 ≤ p` and `1 ≤ log p`!
      push Not at hL_small
      have hsum_log : ∑ p ∈ S_hi, Real.log (p : ℝ) ≤ L := by
        have h1 : ∏ p ∈ S_hi, p ∣ n :=
          dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)) (Nat.prod_primeFactors_dvd n)
        have h2 : (∏ p ∈ S_hi, (p : ℝ)) ≤ 2 * (n : ℝ) := by
          have : (∏ p ∈ S_hi, (p : ℝ)) ≤ (n : ℝ) := by
            rw [← Nat.cast_prod]; exact Nat.cast_le.mpr (Nat.le_of_dvd hn h1)
          linarith [Nat.cast_nonneg (α := ℝ) n]
        have hpos_prod : 0 < ∏ p ∈ S_hi, (p : ℝ) :=
          Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
        rw [← Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos.ne']
        exact Real.log_le_log hpos_prod h2
      have hterm3 : ∀ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1) ≤ (2 / Real.sqrt L) * Real.log (p : ℝ) := by
        intro p hp
        have hp_gt : L < (p : ℝ) := by
          have hnot : ¬ (p ≤ Z) := (Finset.mem_filter.mp hp).2
          have h1 := Nat.lt_floor_add_one L
          have h2 : ((Z + 1 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr (by omega)
          push_cast at h2; linarith
        have hlog1 : (1 : ℝ) ≤ Real.log (p : ℝ) := by
          have h3 : Real.exp 1 ≤ (p : ℝ) := by linarith [Real.exp_one_lt_d9]
          have := Real.log_le_log (Real.exp_pos 1) h3; rwa [Real.log_exp] at this
        have hsq_le : Real.sqrt L ≤ Real.sqrt (p : ℝ) := Real.sqrt_le_sqrt hp_gt.le
        calc Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
            ≤ 2 / Real.sqrt (p : ℝ) := hterm_le p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
          _ ≤ 2 / Real.sqrt L := div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hL_pos) hsq_le
          _ ≤ (2 / Real.sqrt L) * Real.log (p : ℝ) := le_mul_of_one_le_right (by positivity) hlog1
      calc ∑ p ∈ S_hi, Real.sqrt (p : ℝ) / ((p : ℝ) - 1)
          ≤ ∑ p ∈ S_hi, (2 / Real.sqrt L) * Real.log (p : ℝ) := Finset.sum_le_sum hterm3
        _ = (2 / Real.sqrt L) * ∑ p ∈ S_hi, Real.log (p : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ (2 / Real.sqrt L) * L := mul_le_mul_of_nonneg_left hsum_log (by positivity)
        _ = 2 * Real.sqrt L := by
            have hsq : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL_pos).ne'
            field_simp [hsq]; rw [Real.sq_sqrt hL_pos.le]
  linarith

/-- **Subexponential Rankin tail bound `(2)`:**
For any `r, n, P ≥ 1` and finite upper cutoff `M`,
`∑_{P < q ≤ M, (q,r)=1} ‖A_q(n;r)‖ ≤ (exp 8 / √P) * exp(6 * √(log(2n)))`. -/
theorem rankin_tail_bound {r n P M : ℕ} (hn : 0 < n) (hP : 1 ≤ P) :
    ∑ q ∈ (Finset.Icc (P + 1) M).filter (fun q => Nat.Coprime q r),
      ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ ≤
        (Real.exp 8 / Real.sqrt (P : ℝ)) * Real.exp (6 * Real.sqrt (Real.log (2 * (n : ℝ)))) := by
  let Qset := ((Finset.Icc (P + 1) M).filter (fun q => Nat.Coprime q r)).filter Squarefree
  have hdrop : ∑ q ∈ (Finset.Icc (P + 1) M).filter (fun q => Nat.Coprime q r),
        ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ =
      ∑ q ∈ Qset, ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hnot => ?_
    have hnsf : ¬ Squarefree q := fun hsf => hnot (Finset.mem_filter.mpr ⟨hq, hsf⟩)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsf]; simp
  rw [hdrop]
  -- Each squarefree term equals `∏_{p ∣ q} |localFactor r n p|`.
  have hterm : ∀ q ∈ Qset,
      ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ ≤
        (1 / Real.sqrt (P : ℝ)) *
          ∏ p ∈ q.primeFactors, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
    intro q hq
    have hq_mem := Finset.mem_filter.mp hq
    have hq_sf := hq_mem.2
    have hq_r := (Finset.mem_filter.mp hq_mem.1).2
    have hq_Icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq_mem.1).1
    have hq_pos : 0 < q := by omega
    have hq_gt : (P : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr (by omega)
    have hP_pos : (0 : ℝ) < P := Nat.cast_pos.mpr hP
    -- Show `‖A_q‖ = ∏ p ∈ q.primeFactors, |localFactor r n p|`.
    have hfac : ((ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2) =
        ((∏ p ∈ q.primeFactors, localFactor r n p : ℝ) : ℂ) := by
      have hgen : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ Nat.Coprime p r) →
          ((∏ p ∈ T, localFactor r n p : ℝ) : ℂ) =
            (ArithmeticFunction.moebius (∏ p ∈ T, p) : ℂ) ^ 2 *
              ramanujanSum (∏ p ∈ T, p) n / ((∏ p ∈ T, p).totient : ℂ) ^ 2 := by
        intro T hT
        induction T using Finset.induction_on with
        | empty => simp [ramanujanSum_one]
        | @insert p s hp ih =>
          rw [Finset.prod_insert hp, Finset.prod_insert hp]
          have hp' := hT p (Finset.mem_insert_self _ _)
          have hs' : ∀ x ∈ s, x.Prime ∧ Nat.Coprime x r := fun x hx => hT x (Finset.mem_insert_of_mem hx)
          have hcop : Nat.Coprime p (∏ x ∈ s, x) := Nat.Coprime.prod_right fun x hx =>
            (Nat.coprime_primes hp'.1 (hs' x hx).1).2 (fun h => hp (h ▸ hx))
          have hs_pos : 0 < ∏ x ∈ s, x := Finset.prod_pos fun x hx => (hs' x hx).1.pos
          rw [Complex.ofReal_mul, localFactor_eq_complex hp'.1, ite_eq_left hp'.2, ih hs',
              ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
              ramanujanSum_mul_of_coprime hp'.1.pos hs_pos hcop, Nat.totient_mul hcop]
          push_cast; ring
      have h1 := hgen q.primeFactors fun p hp =>
        ⟨Nat.prime_of_mem_primeFactors hp, hq_r.coprime_dvd_left (Nat.mem_primeFactors.mp hp).2.1⟩
      rw [Nat.prod_primeFactors_of_squarefree hq_sf] at h1
      exact h1.symm
    have hnorm : ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ =
        ∏ p ∈ q.primeFactors, |localFactor r n p| := by
      rw [hfac, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
    have hsqrt_q : Real.sqrt (q : ℝ) = ∏ p ∈ q.primeFactors, Real.sqrt (p : ℝ) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hq_sf, Nat.cast_prod]
      exact Real.sqrt_prod _ (fun _ _ => Nat.cast_nonneg _)
    rw [hnorm, Finset.prod_mul_distrib, ← hsqrt_q]
    have hratio : (1 : ℝ) ≤ (1 / Real.sqrt (P : ℝ)) * Real.sqrt (q : ℝ) := by
      rw [one_div_mul_eq_div, one_le_div (Real.sqrt_pos.mpr hP_pos)]
      exact Real.sqrt_le_sqrt hq_gt
    calc ∏ p ∈ q.primeFactors, |localFactor r n p|
        = 1 * ∏ p ∈ q.primeFactors, |localFactor r n p| := (one_mul _).symm
      _ ≤ ((1 / Real.sqrt (P : ℝ)) * Real.sqrt (q : ℝ)) * ∏ p ∈ q.primeFactors, |localFactor r n p| :=
          mul_le_mul_of_nonneg_right hratio (Finset.prod_nonneg fun _ _ => abs_nonneg _)
      _ = (1 / Real.sqrt (P : ℝ)) * (Real.sqrt (q : ℝ) * ∏ p ∈ q.primeFactors, |localFactor r n p|) := by ring
  let S := (Finset.Icc 1 M).filter Nat.Prime
  have hsum_le : ∑ q ∈ Qset, ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ ≤
      (1 / Real.sqrt (P : ℝ)) * ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) := by
    have h1 : ∑ q ∈ Qset, ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖ ≤
        (1 / Real.sqrt (P : ℝ)) * ∑ q ∈ Qset, ∏ p ∈ q.primeFactors, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hpow : ∑ T ∈ S.powerset, ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) =
        ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) := by
      have h := Finset.prod_add (f := fun p : ℕ => Real.sqrt (p : ℝ) * |localFactor r n p|)
        (g := fun _ => (1 : ℝ)) S
      simpa [add_comm] using h.symm
    rw [← hpow]
    calc ∑ q ∈ Qset, ∏ p ∈ q.primeFactors, (Real.sqrt (p : ℝ) * |localFactor r n p|)
        = ∑ T ∈ Qset.image Nat.primeFactors, ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
          symm; refine Finset.sum_image fun q₁ hq₁ q₂ hq₂ hEq => ?_
          rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hq₁).2,
              ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hq₂).2, hEq]
      _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (Real.sqrt (p : ℝ) * |localFactor r n p|) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
            (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hT
          have hqIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
          exact Finset.mem_powerset.mpr fun p hp =>
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
              (Nat.le_of_dvd (by omega) (Nat.mem_primeFactors.mp hp).2.1).trans hqIcc.2⟩,
              Nat.prime_of_mem_primeFactors hp⟩
  -- Split `∏ p ∈ S` into `p ∣ n` and `¬ p ∣ n`.
  have hsplit_prod : ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) ≤
      (∏ p ∈ n.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1))) *
      (∏ p ∈ S, (1 + Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2))) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (fun p => p ∣ n)]
    refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => by positivity)
      (Finset.prod_nonneg fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
        have : 0 ≤ Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
        linarith)
    · have hsub : S.filter (fun p => p ∣ n) ⊆ n.primeFactors := fun p hp =>
        Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2,
          (Finset.mem_filter.mp hp).2, hn.ne'⟩
      calc ∏ p ∈ S.filter (fun p => p ∣ n), (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)
          ≤ ∏ p ∈ S.filter (fun p => p ∣ n), (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) := by
            refine real_prod_le_prod _ _ _ (fun _ _ => by positivity) fun p hp => ?_
            have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp_pr.two_le
            have hpd := (Finset.mem_filter.mp hp).2
            unfold localFactor
            by_cases hpr : p ∣ r
            · simp only [hpr, ↓reduceIte, abs_zero, mul_zero]
              have : 0 ≤ Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
              linarith
            · simp only [hpr, ↓reduceIte, hpd, abs_of_nonneg (show 0 ≤ 1 / ((p : ℝ) - 1) by
                exact div_nonneg zero_le_one (by linarith))]
              rw [mul_one_div]
        _ ≤ ∏ p ∈ n.primeFactors, (1 + Real.sqrt (p : ℝ) / ((p : ℝ) - 1)) :=
            real_prod_le_prod_of_subset_of_one_le hsub
              (fun p hp => by
                have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (hsub hp)).two_le
                have : 0 ≤ Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
                linarith)
              (fun p hp _ => by
                have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
                have : 0 ≤ Real.sqrt (p : ℝ) / ((p : ℝ) - 1) := div_nonneg (Real.sqrt_nonneg _) (by linarith)
                linarith)
    · calc ∏ p ∈ S.filter (fun p => ¬ p ∣ n), (1 + Real.sqrt (p : ℝ) * |localFactor r n p|)
          ≤ ∏ p ∈ S.filter (fun p => ¬ p ∣ n), (1 + Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
            refine real_prod_le_prod _ _ _ (fun _ _ => by positivity) fun p hp => ?_
            have hp_pr := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
            have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp_pr.two_le
            have hnpd := (Finset.mem_filter.mp hp).2
            unfold localFactor
            by_cases hpr : p ∣ r
            · simp only [hpr, ↓reduceIte, abs_zero, mul_zero]
              have : 0 ≤ Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2) := div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
              linarith
            · simp only [hpr, ↓reduceIte, hnpd, abs_neg, abs_of_nonneg (show 0 ≤ 1 / (((p : ℝ) - 1) ^ 2) by
                exact div_nonneg zero_le_one (sq_nonneg _))]
              rw [mul_one_div]
        _ ≤ ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)) :=
            real_prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
              (fun _ _ => by positivity)
              (fun p hp _ => by
                have : 0 ≤ Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2) := div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
                linarith)
  have hnondiv : ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤ Real.exp 8 := by
    have hprod_exp : ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤
        Real.exp (∑ p ∈ S, Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
      rw [Real.exp_sum]
      refine real_prod_le_prod S _ _ (fun _ _ => by positivity) fun p _ => by
        linarith [Real.add_one_le_exp (Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2))]
    refine hprod_exp.trans (Real.exp_le_exp.mpr ?_)
    have hsub : S ⊆ Finset.Icc 2 M := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.two_le, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
    have htele : ∀ N : ℕ,
        ∑ m ∈ Finset.Icc 2 N, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) ≤ 1 := by
      intro N
      by_cases hN0 : N = 0
      · subst hN0; simp
      · have hN1 : 1 ≤ N := Nat.pos_of_ne_zero hN0
        have heq : ∀ k : ℕ, 1 ≤ k →
            ∑ m ∈ Finset.Icc 2 k, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
              1 - 1 / Real.sqrt (k : ℝ) := by
          intro k hk
          induction k with
          | zero => omega
          | succ n ih =>
            rcases eq_or_lt_of_le (Nat.zero_le n) with rfl | hn_pos
            · simp
            · have hsplit : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hsplit, Finset.sum_insert (by simp), ih hn_pos]
              simp only [Nat.add_sub_cancel]
              ring
        rw [heq N hN1]
        have : 0 ≤ 1 / Real.sqrt (N : ℝ) := by positivity
        linarith
    calc ∑ p ∈ S, Real.sqrt (p : ℝ) / (((p : ℝ) - 1) ^ 2)
        ≤ ∑ m ∈ Finset.Icc 2 M, Real.sqrt (m : ℝ) / (((m : ℝ) - 1) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ ∑ m ∈ Finset.Icc 2 M,
            8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm2_nat : 2 ≤ m := (Finset.mem_Icc.mp hm).1
          have hm2 : (2 : ℝ) ≤ m := Nat.cast_le.mpr hm2_nat
          have hm1_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
          rw [hm1_cast]
          have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
          have hsm1 : 0 < Real.sqrt ((m : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
          have hsm_le : Real.sqrt ((m : ℝ) - 1) ≤ Real.sqrt (m : ℝ) :=
            Real.sqrt_le_sqrt (by linarith)
          have hdiff : 1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt (m : ℝ) =
              1 / (Real.sqrt ((m : ℝ) - 1) * Real.sqrt (m : ℝ) *
                (Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1))) := by
            have hsq_sub : (Real.sqrt (m : ℝ) - Real.sqrt ((m : ℝ) - 1)) *
                (Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1)) = 1 := by
              have h1 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
              have h2 : Real.sqrt ((m : ℝ) - 1) ^ 2 = (m : ℝ) - 1 := Real.sq_sqrt (by linarith)
              nlinarith
            have hsum_pos : 0 < Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1) := by linarith
            field_simp [hsm.ne', hsm1.ne', hsum_pos.ne']
            linarith
          have hden_le : Real.sqrt ((m : ℝ) - 1) * Real.sqrt (m : ℝ) *
              (Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1)) ≤ 2 * (m : ℝ) * Real.sqrt (m : ℝ) := by
            have h1 : Real.sqrt ((m : ℝ) - 1) * Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
              calc Real.sqrt ((m : ℝ) - 1) * Real.sqrt (m : ℝ)
                  ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) :=
                    mul_le_mul_of_nonneg_right hsm_le hsm.le
                _ = (m : ℝ) := Real.mul_self_sqrt (by linarith)
            have h2 : Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1) ≤ 2 * Real.sqrt (m : ℝ) := by
              linarith
            nlinarith [mul_le_mul h1 h2 (by positivity) (by positivity)]
          have hstep1 : 4 / ((m : ℝ) * Real.sqrt (m : ℝ)) ≤
              8 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt (m : ℝ)) := by
            rw [hdiff, mul_one_div]
            have hden_pos : 0 < Real.sqrt ((m : ℝ) - 1) * Real.sqrt (m : ℝ) *
                (Real.sqrt (m : ℝ) + Real.sqrt ((m : ℝ) - 1)) := by positivity
            rw [div_le_div_iff₀ (by positivity) hden_pos]
            nlinarith
          have hstep2 : Real.sqrt (m : ℝ) / (((m : ℝ) - 1) ^ 2) ≤
              4 / ((m : ℝ) * Real.sqrt (m : ℝ)) := by
            rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
            have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
              Real.mul_self_sqrt (by linarith)
            have hmul : Real.sqrt (m : ℝ) * ((m : ℝ) * Real.sqrt (m : ℝ)) = (m : ℝ) ^ 2 := by
              calc Real.sqrt (m : ℝ) * ((m : ℝ) * Real.sqrt (m : ℝ))
                  = (m : ℝ) * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) := by ring
                _ = (m : ℝ) * (m : ℝ) := by rw [hsq]
                _ = (m : ℝ) ^ 2 := by ring
            rw [hmul]; nlinarith
          exact hstep2.trans hstep1
      _ = 8 * ∑ m ∈ Finset.Icc 2 M,
            (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ 8 * 1 := mul_le_mul_of_nonneg_left (htele M) (by norm_num)
      _ = 8 := by norm_num
  calc ∑ q ∈ Qset, ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 * ramanujanSum q n / (q.totient : ℂ) ^ 2‖
      ≤ (1 / Real.sqrt (P : ℝ)) * ∏ p ∈ S, (1 + Real.sqrt (p : ℝ) * |localFactor r n p|) := hsum_le
    _ ≤ (1 / Real.sqrt (P : ℝ)) * (Real.exp (6 * Real.sqrt (Real.log (2 * (n : ℝ)))) * Real.exp 8) :=
        mul_le_mul_of_nonneg_left (hsplit_prod.trans (mul_le_mul (prod_dvd_one_add_sqrt_div_pred_le hn) hnondiv
          (Finset.prod_nonneg fun _ _ => by positivity) (by positivity))) (by positivity)
    _ = (Real.exp 8 / Real.sqrt (P : ℝ)) * Real.exp (6 * Real.sqrt (Real.log (2 * (n : ℝ)))) := by ring

end SubexponentialRankinTail

section ArithmeticMoments

/-- `∑_{d ∈ Icc 1 N, Squarefree d} 1 / φ(d)² ≤ 4`. -/
lemma sum_sqfree_inv_totient_sq_le_four (N : ℕ) :
    ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d.totient : ℝ) ^ 2) ≤ 4 := by
  let S := (Finset.Icc 2 N).filter Nat.Prime
  let Sodd := (Finset.Icc 3 N).filter Nat.Prime
  have h1 : ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d.totient : ℝ) ^ 2) ≤
      ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) := by
    have hpow : ∑ T ∈ S.powerset, ∏ p ∈ T, ((1 : ℝ) / (((p : ℝ) - 1) ^ 2)) =
        ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) := by
      have h := Finset.prod_add (f := fun p : ℕ => (1 : ℝ) / (((p : ℝ) - 1) ^ 2)) (g := fun _ => (1 : ℝ)) S
      simpa [add_comm] using h.symm
    rw [← hpow]
    have hrew : ∀ d ∈ (Finset.Icc 1 N).filter Squarefree,
        (1 : ℝ) / ((d.totient : ℝ) ^ 2) = ∏ p ∈ d.primeFactors, (1 / (((p : ℝ) - 1) ^ 2)) := by
      intro d hd
      have hd1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
      have hsf := (Finset.mem_filter.mp hd).2
      rw [totient_eq_prod_sub_one_of_squarefree hd1 hsf, ← Finset.prod_pow]
      simp_rw [one_div]; rw [← Finset.prod_inv_distrib]
    calc ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d.totient : ℝ) ^ 2)
        = ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, ∏ p ∈ d.primeFactors, (1 / (((p : ℝ) - 1) ^ 2)) :=
          Finset.sum_congr rfl hrew
      _ = ∑ T ∈ ((Finset.Icc 1 N).filter Squarefree).image Nat.primeFactors,
            ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) := by
          symm; refine Finset.sum_image fun d₁ hd₁ d₂ hd₂ hEq => ?_
          rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₁).2,
              ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₂).2, hEq]
      _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (1 / (((p : ℝ) - 1) ^ 2)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
            (fun _ _ _ => Finset.prod_nonneg fun _ _ => by positivity)
          obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
          have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
          exact Finset.mem_powerset.mpr fun p hp =>
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
              (Nat.le_of_dvd hdIcc.1 (Nat.mem_primeFactors.mp hp).2.1).trans hdIcc.2⟩,
              Nat.prime_of_mem_primeFactors hp⟩
  have h2 : ∏ p ∈ S, (1 + 1 / (((p : ℝ) - 1) ^ 2)) ≤ 2 * Real.exp (1 / 2 : ℝ) := by
    have hodd_le := prod_odd_prime_one_add_inv_pred_sq_le Sodd fun p hp =>
      ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
    by_cases h2N : 2 ≤ N
    · have h2mem : (2 : ℕ) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, h2N⟩, Nat.prime_two⟩
      have herase : S.erase 2 = Sodd := by
        ext p; simp only [S, Sodd, Finset.mem_erase, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hne, ⟨h1, h2⟩, hp⟩; exact ⟨⟨by omega, h2⟩, hp⟩
        · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨by omega, ⟨by omega, h2⟩, hp⟩
      rw [← Finset.mul_prod_erase S _ h2mem, herase]
      have h2val : (1 : ℝ) + 1 / (((2 : ℕ) : ℝ) - 1) ^ 2 = 2 := by norm_num
      rw [h2val]; linarith
    · have hSempty : S = Sodd := by
        ext p; simp only [S, Sodd, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, hp⟩; omega
        · rintro ⟨⟨h1, h2⟩, hp⟩; omega
      rw [hSempty]; linarith [Real.exp_pos (1 / 2 : ℝ)]
  linarith [exp_half_le_seven_fourths]

/-- **Arithmetic sum `(3)` (second half):**
`∑_{q ≤ Q, (q,r)=1, sqfree} q / φ(q)² ≤ 72 * (φ(r) / r) * log(2 * Y)`. -/
theorem sum_coprime_sqfree_div_totient_sq_le {r Q Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hQY : Q ≤ Y)
    (hY_large : 2 ^ 72 ≤ Y) :
    ∑ q ∈ ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)).filter Squarefree,
      ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
        72 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
  let Qset := ((Finset.Icc 1 Q).filter (fun q => Nat.Coprime q r)).filter Squarefree
  let Dset := (Finset.Icc 1 Q).filter Squarefree
  -- Rewrite `q / φ(q)² = (1 / φ(q)) * ∑_{d ∣ q} 1 / φ(d)` and swap `q = d * m`.
  have hle : ∑ q ∈ Qset, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
      (∑ d ∈ Dset, (1 : ℝ) / ((d.totient : ℝ) ^ 2)) *
        (∑ m ∈ Qset, (1 : ℝ) / (m.totient : ℝ)) := by
    have hrew : ∑ q ∈ Qset, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) =
        ∑ q ∈ Qset, ∑ d ∈ Dset,
          (if d ∣ q then (1 : ℝ) / ((d.totient : ℝ) * (q.totient : ℝ)) else 0) := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
      have hq2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2
      have hqsf := (Finset.mem_filter.mp hq).2
      have hdiv := sqfree_div_totient_eq_sum_divisors hq1 hqsf
      have hqtot_ne : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hq1).ne'
      have hmul : (q : ℝ) / ((q.totient : ℝ) ^ 2) =
          (1 / (q.totient : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) := by field_simp [hqtot_ne]
      rw [hmul, hdiv, Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun d _ => by ring
      ext d; simp only [Dset, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨hdvd, _⟩
        exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdvd hq1, (Nat.le_of_dvd hq1 hdvd).trans hq2⟩,
          hqsf.squarefree_of_dvd hdvd⟩, hdvd⟩
      · rintro ⟨_, hdvd⟩; exact ⟨hdvd, by omega⟩
    rw [hrew, Finset.sum_comm]
    calc ∑ d ∈ Dset, ∑ q ∈ Qset,
            (if d ∣ q then (1 : ℝ) / ((d.totient : ℝ) * (q.totient : ℝ)) else 0)
        ≤ ∑ d ∈ Dset, ((1 : ℝ) / ((d.totient : ℝ) ^ 2)) * ∑ m ∈ Qset, (1 : ℝ) / (m.totient : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          have hsub : (Qset.filter (fun q => d ∣ q)).image (fun q => q / d) ⊆ Qset := by
            intro m hm
            obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
            have hq_mem := (Finset.mem_filter.mp hq).1
            have hdvd := (Finset.mem_filter.mp hq).2
            have hq_sf := (Finset.mem_filter.mp hq_mem).2
            have hq_r := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem).1).2
            have hqIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem).1).1
            exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨
              Nat.div_pos (Nat.le_of_dvd hqIcc.1 hdvd) hd_pos, (Nat.div_le_self q d).trans hqIcc.2⟩,
              hq_r.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd)⟩,
              hq_sf.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd)⟩
          have hrew2 : ∑ q ∈ Qset.filter (fun q => d ∣ q),
                (1 : ℝ) / ((d.totient : ℝ) * (q.totient : ℝ)) =
              ∑ m ∈ (Qset.filter (fun q => d ∣ q)).image (fun q => q / d),
                ((1 : ℝ) / ((d.totient : ℝ) ^ 2)) * ((1 : ℝ) / (m.totient : ℝ)) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl fun q hq => ?_
              have hq_sf := (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
              have hdvd := (Finset.mem_filter.mp hq).2
              have hmul_eq : d * (q / d) = q := Nat.mul_div_cancel' hdvd
              have hcop : Nat.Coprime d (q / d) := by
                apply Nat.coprime_of_dvd
                intro s hs hsd hsm
                exact hs.not_isUnit (hq_sf s (by rw [← hmul_eq]; exact mul_dvd_mul hsd hsm))
              have htot : q.totient = d.totient * (q / d).totient := by
                conv_lhs => rw [← hmul_eq]
                exact Nat.totient_mul hcop
              rw [htot]; push_cast; ring
            · intro q₁ hq₁ q₂ hq₂ hEq
              dsimp only at hEq
              rw [← Nat.mul_div_cancel' (Finset.mem_filter.mp hq₁).2,
                  ← Nat.mul_div_cancel' (Finset.mem_filter.mp hq₂).2, hEq]
          rw [hrew2]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (∑ d ∈ Dset, (1 : ℝ) / ((d.totient : ℝ) ^ 2)) * ∑ m ∈ Qset, (1 : ℝ) / (m.totient : ℝ) :=
          (Finset.sum_mul _ _ _).symm
  have h2 := sum_coprime_inv_totient_le hr hrY hQY hY_large
  have h1 := sum_sqfree_inv_totient_sq_le_four Q
  calc ∑ q ∈ Qset, ((q : ℝ) / ((q.totient : ℝ) ^ 2))
      ≤ (∑ d ∈ Dset, (1 : ℝ) / ((d.totient : ℝ) ^ 2)) * ∑ m ∈ Qset, (1 : ℝ) / (m.totient : ℝ) := hle
    _ ≤ 4 * (18 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ))) :=
        mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ = 72 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by ring

/-- Elementary binomial bound: `(1 + x)^k - 1 ≤ (2^k - 1) * x` for `0 ≤ x ≤ 1`. -/
lemma one_add_pow_sub_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : ℕ) :
    (1 + x) ^ k - 1 ≤ ((2 : ℝ) ^ k - 1) * x := by
  induction k with
  | zero => simp
  | succ m ih =>
    have h1x : (1 + x) ^ m ≤ (2 : ℝ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    have hpow : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) + (1 + x) ^ m * x := by ring
    have h2 : ((2 : ℝ) ^ (m + 1) - 1) * x = ((2 : ℝ) ^ m - 1) * x + (2 : ℝ) ^ m * x := by ring
    rw [hpow, h2]
    exact add_le_add ih (mul_le_mul_of_nonneg_right h1x hx0)

/-- **General `g(q)^k` moment bound:** For all `k, Z : ℕ`,
`∑ q ∈ Icc 1 Z, (q / φ(q))^k ≤ exp(2^k) * Z`. -/
theorem sum_div_totient_pow_le (k Z : ℕ) :
    ∑ q ∈ Finset.Icc 1 Z, ((q : ℝ) / (q.totient : ℝ)) ^ k ≤ Real.exp ((2 : ℝ) ^ k) * (Z : ℝ) := by
  let Ck : ℝ := (2 : ℝ) ^ k
  have hCk_nn : 0 ≤ Ck := by positivity
  -- Pointwise bound `(q / φ(q))^k ≤ ∑_{d ∣ q, sqfree} ∏_{p ∣ d} (Ck / (p - 1))`.
  have hpt : ∀ q ∈ Finset.Icc 1 Z,
      ((q : ℝ) / (q.totient : ℝ)) ^ k ≤
        ∑ d ∈ (Finset.Icc 1 Z).filter Squarefree,
          if d ∣ q then ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) - 1)) else 0 := by
    intro q hq
    have hq1 := (Finset.mem_Icc.mp hq).1
    have hq2 := (Finset.mem_Icc.mp hq).2
    rw [div_totient_eq_prod_primeFactors hq1, ← Finset.prod_pow]
    have h1 : ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ k ≤
        ∏ p ∈ q.primeFactors, (1 + Ck / ((p : ℝ) - 1)) := by
      refine real_prod_le_prod q.primeFactors _ _ (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
        exact pow_nonneg (div_nonneg (by linarith) (by linarith)) k) (fun p hp => ?_)
      have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
      have hrew : (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) := by
        field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]; ring
      rw [hrew]
      have hx0 : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) := div_nonneg zero_le_one (by linarith)
      have hx1 : 1 / ((p : ℝ) - 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
      have hb := one_add_pow_sub_one_le hx0 hx1 k
      have hCk_gt : (2 : ℝ) ^ k - 1 ≤ Ck := by dsimp [Ck]; linarith
      calc (1 + 1 / ((p : ℝ) - 1)) ^ k
          ≤ 1 + ((2 : ℝ) ^ k - 1) * (1 / ((p : ℝ) - 1)) := by linarith
        _ ≤ 1 + Ck * (1 / ((p : ℝ) - 1)) := by
            linarith [mul_le_mul_of_nonneg_right hCk_gt hx0]
        _ = 1 + Ck / ((p : ℝ) - 1) := by ring
    refine h1.trans ?_
    have hexp : ∏ p ∈ q.primeFactors, (1 + Ck / ((p : ℝ) - 1)) =
        ∑ T ∈ q.primeFactors.powerset, ∏ p ∈ T, (Ck / ((p : ℝ) - 1)) := by
      have h := Finset.prod_add (f := fun p : ℕ => Ck / ((p : ℝ) - 1)) (g := fun _ => (1 : ℝ)) q.primeFactors
      simpa only [add_comm, Finset.prod_const_one, mul_one] using h
    rw [hexp, ← Finset.sum_filter]
    -- Map `T ↦ ∏ p ∈ T, p` bijectively to `((Icc 1 Z).filter Squarefree).filter (· ∣ q)`.
    refine le_of_eq (Finset.sum_bij (fun T _ => ∏ p ∈ T, p) ?_ ?_ ?_ ?_)
    · intro T hT
      have hTsub := Finset.mem_powerset.mp hT
      have hdvd : (∏ p ∈ T, p) ∣ q :=
        dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hTsub) (Nat.prod_primeFactors_dvd q)
      have hpos : 0 < ∏ p ∈ T, p := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (hTsub hp)).pos
      have hsf : Squarefree (∏ p ∈ T, p) := by
        clear hdvd hpos h1 hexp
        induction T using Finset.induction_on with
        | empty => simp
        | @insert p s hp ih =>
          rw [Finset.prod_insert hp]
          have hpsub : p ∈ q.primeFactors := hTsub (Finset.mem_insert_self _ _)
          have hssub : s ⊆ q.primeFactors := fun x hx => hTsub (Finset.mem_insert_of_mem hx)
          have hcop : Nat.Coprime p (∏ x ∈ s, x) := Nat.Coprime.prod_right fun x hx =>
            (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hpsub)
              (Nat.prime_of_mem_primeFactors (hssub hx))).2 (fun h => hp (h ▸ hx))
          exact (Nat.squarefree_mul hcop).mpr ⟨(Nat.prime_of_mem_primeFactors hpsub).squarefree,
            ih (Finset.mem_powerset.mpr hssub) hssub⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, (Nat.le_of_dvd hq1 hdvd).trans hq2⟩, hsf⟩, hdvd⟩
    · intro T₁ hT₁ T₂ hT₂ hEq
      have hpf : ∀ T ⊆ q.primeFactors, (∏ p ∈ T, p).primeFactors = T := by
        intro T hTsub
        induction T using Finset.induction_on with
        | empty => simp
        | @insert p s hp ih =>
          rw [Finset.prod_insert hp]
          have hpsub : p ∈ q.primeFactors := hTsub (Finset.mem_insert_self _ _)
          have hssub : s ⊆ q.primeFactors := fun x hx => hTsub (Finset.mem_insert_of_mem hx)
          have hpr := Nat.prime_of_mem_primeFactors hpsub
          have hs_pos : 0 < ∏ x ∈ s, x := Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors (hssub hx)).pos
          rw [Nat.primeFactors_mul hpr.ne_zero hs_pos.ne', hpr.primeFactors, ih hssub]
          ext x; simp [Finset.mem_insert]
      rw [← hpf T₁ (Finset.mem_powerset.mp hT₁), ← hpf T₂ (Finset.mem_powerset.mp hT₂), hEq]
    · intro d hd
      have hd_sf := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
      have hd_dvd := (Finset.mem_filter.mp hd).2
      refine ⟨d.primeFactors, Finset.mem_powerset.mpr fun p hp => ?_, Nat.prod_primeFactors_of_squarefree hd_sf⟩
      have hpm := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primeFactors.mpr ⟨hpm.1, dvd_trans hpm.2.1 hd_dvd, (by omega : q ≠ 0)⟩
    · intro T hT
      have hTsub := Finset.mem_powerset.mp hT
      have hpf : (∏ p ∈ T, p).primeFactors = T := by
        induction T using Finset.induction_on with
        | empty => simp
        | @insert p s hp ih =>
          rw [Finset.prod_insert hp]
          have hpsub : p ∈ q.primeFactors := hTsub (Finset.mem_insert_self _ _)
          have hssub : s ⊆ q.primeFactors := fun x hx => hTsub (Finset.mem_insert_of_mem hx)
          have hpr := Nat.prime_of_mem_primeFactors hpsub
          have hs_pos : 0 < ∏ x ∈ s, x := Finset.prod_pos fun x hx => (Nat.prime_of_mem_primeFactors (hssub hx)).pos
          rw [Nat.primeFactors_mul hpr.ne_zero hs_pos.ne', hpr.primeFactors,
              ih (Finset.mem_powerset.mpr hssub) hssub]
          ext x; simp [Finset.mem_insert]
      rw [hpf]
  -- Swap sum and bound `# {q ∈ Icc 1 Z : d ∣ q} ≤ Z / d`.
  let Dset := (Finset.Icc 1 Z).filter Squarefree
  have hswap : ∑ q ∈ Finset.Icc 1 Z, ((q : ℝ) / (q.totient : ℝ)) ^ k ≤
      (Z : ℝ) * ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
    calc ∑ q ∈ Finset.Icc 1 Z, ((q : ℝ) / (q.totient : ℝ)) ^ k
        ≤ ∑ q ∈ Finset.Icc 1 Z, ∑ d ∈ Dset,
            if d ∣ q then ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) - 1)) else 0 := Finset.sum_le_sum hpt
      _ = ∑ d ∈ Dset, ∑ q ∈ Finset.Icc 1 Z,
            if d ∣ q then ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) - 1)) else 0 := Finset.sum_comm
      _ ≤ ∑ d ∈ Dset, ((Z : ℝ) / (d : ℝ)) * ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) - 1)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          have hcard : ((Finset.Icc 1 Z).filter (fun q => d ∣ q)).card ≤ Z / d := by
            have hsub : (Finset.Icc 1 Z).filter (fun q => d ∣ q) ⊆
                (Finset.Icc 1 (Z / d)).image (fun m => d * m) := by
              intro q hq
              obtain ⟨m, rfl⟩ := (Finset.mem_filter.mp hq).2
              have hqIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
              exact Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨Nat.pos_of_mul_pos_left hqIcc.1,
                (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; exact hqIcc.2)⟩, rfl⟩
            calc ((Finset.Icc 1 Z).filter (fun q => d ∣ q)).card
                ≤ ((Finset.Icc 1 (Z / d)).image (fun m => d * m)).card := Finset.card_le_card hsub
              _ ≤ (Finset.Icc 1 (Z / d)).card := Finset.card_image_le
              _ = Z / d := by simp [Nat.card_Icc]
          have hcardR : (((Finset.Icc 1 Z).filter (fun q => d ∣ q)).card : ℝ) ≤ (Z : ℝ) / (d : ℝ) := by
            have h1 : (((Finset.Icc 1 Z).filter (fun q => d ∣ q)).card : ℝ) ≤ ((Z / d : ℕ) : ℝ) :=
              Nat.cast_le.mpr hcard
            have h2 : ((Z / d : ℕ) : ℝ) ≤ (Z : ℝ) / (d : ℝ) := by
              rw [le_div_iff₀ (Nat.cast_pos.mpr hd_pos)]
              exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Z d)
            linarith
          exact mul_le_mul_of_nonneg_right hcardR (Finset.prod_nonneg fun p hp => by
            have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
            exact div_nonneg hCk_nn (by linarith))
      _ = (Z : ℝ) * ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d hd => ?_
          have hsf := (Finset.mem_filter.mp hd).2
          have hd_eq : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
            rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
          rw [div_mul_eq_mul_div, mul_div_assoc, hd_eq, ← Finset.prod_div_distrib]
          congr 1; refine Finset.prod_congr rfl fun p hp => ?_
          have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
          field_simp [(by linarith : (p : ℝ) ≠ 0), (by linarith : (p : ℝ) - 1 ≠ 0)]
  -- Bound the squarefree sum by `∏_{p ≤ Z} (1 + Ck / (p*(p-1))) ≤ exp(Ck)`.
  let S := (Finset.Icc 2 Z).filter Nat.Prime
  have hD_le : ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) ≤ Real.exp Ck := by
    have hpow : ∑ T ∈ S.powerset, ∏ p ∈ T, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) =
        ∏ p ∈ S, (1 + Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
      have h := Finset.prod_add (f := fun p : ℕ => Ck / ((p : ℝ) * ((p : ℝ) - 1))) (g := fun _ => (1 : ℝ)) S
      simpa only [add_comm, Finset.prod_const_one, mul_one] using h.symm
    have h1 : ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        ∏ p ∈ S, (1 + Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [← hpow]
      calc ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1)))
          = ∑ T ∈ Dset.image Nat.primeFactors, ∏ p ∈ T, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
            symm; refine Finset.sum_image fun d₁ hd₁ d₂ hd₂ hEq => ?_
            rw [← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₁).2,
                ← Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₂).2, hEq]
        _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun T hT => ?_)
              (fun T hT _ => Finset.prod_nonneg fun p hp => by
                have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Finset.mem_filter.mp (Finset.mem_powerset.mp hT hp)).2.two_le
                exact div_nonneg hCk_nn (by nlinarith))
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
            have hdIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1
            exact Finset.mem_powerset.mpr fun p hp =>
              Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
                (Nat.le_of_dvd hdIcc.1 (Nat.mem_primeFactors.mp hp).2.1).trans hdIcc.2⟩,
                Nat.prime_of_mem_primeFactors hp⟩
    refine h1.trans ?_
    have h2 : ∏ p ∈ S, (1 + Ck / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        Real.exp (∑ p ∈ S, Ck / ((p : ℝ) * ((p : ℝ) - 1))) := by
      rw [Real.exp_sum]
      refine real_prod_le_prod S _ _ (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Finset.mem_filter.mp hp).2.two_le
        have : 0 ≤ Ck / ((p : ℝ) * ((p : ℝ) - 1)) := div_nonneg hCk_nn (by nlinarith)
        linarith) (fun p _ => by linarith [Real.add_one_le_exp (Ck / ((p : ℝ) * ((p : ℝ) - 1)))])
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    have hsub : S ⊆ Finset.Icc 2 Z := fun p hp => (Finset.mem_filter.mp hp).1
    calc ∑ p ∈ S, Ck / ((p : ℝ) * ((p : ℝ) - 1))
        = Ck * ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ Ck * ∑ m ∈ Finset.Icc 2 Z, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => by
            have hm2 : (2 : ℝ) ≤ m := Nat.cast_le.mpr (Finset.mem_Icc.mp hm).1
            exact div_nonneg zero_le_one (by nlinarith)) hCk_nn
      _ ≤ Ck * 1 := mul_le_mul_of_nonneg_left (sum_inv_mul_pred_le_one Z) hCk_nn
      _ = Ck := mul_one Ck
  calc ∑ q ∈ Finset.Icc 1 Z, ((q : ℝ) / (q.totient : ℝ)) ^ k
      ≤ (Z : ℝ) * ∑ d ∈ Dset, ∏ p ∈ d.primeFactors, (Ck / ((p : ℝ) * ((p : ℝ) - 1))) := hswap
    _ ≤ (Z : ℝ) * Real.exp Ck := mul_le_mul_of_nonneg_left hD_le (Nat.cast_nonneg Z)
    _ = Real.exp Ck * (Z : ℝ) := mul_comm _ _

/-- **Arithmetic sum `(13)`:** Uniformly in `Q : ℕ` and `D ≥ 1`,
`∑_{q ∈ Icc 1 Q, φ(q) ≤ D} q / φ(q) ≤ (exp 2 + 4 * exp 8) * D`. -/
theorem sum_div_totient_of_totient_le (Q D : ℕ) (hD : 1 ≤ D) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D), ((q : ℝ) / (q.totient : ℝ)) ≤
      (Real.exp 2 + 4 * Real.exp 8) * (D : ℝ) := by
  let A := (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)
  rw [← Finset.sum_filter_add_sum_filter_not A (fun q => q ≤ D)]
  -- Low range `q ≤ D`.
  have hlo : ∑ q ∈ A.filter (fun q => q ≤ D), ((q : ℝ) / (q.totient : ℝ)) ≤ Real.exp 2 * (D : ℝ) := by
    have hsub : A.filter (fun q => q ≤ D) ⊆ Finset.Icc 1 D := fun q hq =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1,
        (Finset.mem_filter.mp hq).2⟩
    calc ∑ q ∈ A.filter (fun q => q ≤ D), ((q : ℝ) / (q.totient : ℝ))
        ≤ ∑ q ∈ Finset.Icc 1 D, ((q : ℝ) / (q.totient : ℝ)) ^ 1 := by
          simpa using Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ ≤ Real.exp ((2 : ℝ) ^ 1) * (D : ℝ) := sum_div_totient_pow_le 1 D
      _ = Real.exp 2 * (D : ℝ) := by norm_num
  -- High range `D < q ≤ Q`: cover by dyadic blocks `2^j * D < q ≤ 2^(j+1) * D`.
  have hhi : ∑ q ∈ A.filter (fun q => ¬ q ≤ D), ((q : ℝ) / (q.totient : ℝ)) ≤
      4 * Real.exp 8 * (D : ℝ) := by
    let J := Q + 1
    let B : ℕ → Finset ℕ := fun j =>
      (Finset.Icc (2 ^ j * D + 1) (2 ^ (j + 1) * D)).filter (fun q => q.totient ≤ D)
    have hcover : A.filter (fun q => ¬ q ≤ D) ⊆ (Finset.range J).biUnion B := by
      intro q hq
      have hq_mem := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
      have hq_leQ := (Finset.mem_Icc.mp hq_mem.1).2
      have hq_tot := hq_mem.2
      have hq_gtD : D < q := by have := (Finset.mem_filter.mp hq).2; omega
      let j := Nat.log 2 ((q - 1) / D)
      have hdiv_pos : 1 ≤ (q - 1) / D := (Nat.le_div_iff_mul_le hD).mpr (by omega)
      have hj_lo : 2 ^ j ≤ (q - 1) / D := Nat.pow_log_le_self 2 (by omega)
      have hj_hi : (q - 1) / D < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hj_lt : j < J := by
        have h1 : j < 2 ^ j := Nat.lt_two_pow_self
        have h2 : 2 ^ j ≤ q := hj_lo.trans ((Nat.div_le_self _ _).trans (by omega))
        omega
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hq_tot⟩⟩
      · have := (Nat.le_div_iff_mul_le hD).mp hj_lo; omega
      · have := (Nat.div_lt_iff_lt_mul hD).mp hj_hi; omega
    have hblock : ∀ j : ℕ, ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ)) ≤
        (2 * Real.exp 8 * (D : ℝ)) * ((1 / 2 : ℝ) ^ j) := by
      intro j
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j * (D : ℝ) := by positivity
      have hpt : ∀ q ∈ B j,
          (q : ℝ) / (q.totient : ℝ) ≤
            ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 2)) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by
        intro q hq
        have hqIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
        have hq_tot : (q.totient : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr (Finset.mem_filter.mp hq).2
        have hq_ge : (2 : ℝ) ^ j * (D : ℝ) ≤ (q : ℝ) := by
          have : 2 ^ j * D ≤ q := by omega
          exact_mod_cast this
        have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
        have htot_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
        have hrat1 : (1 : ℝ) ≤ ((D : ℝ) / (q.totient : ℝ)) ^ 2 :=
          one_le_pow₀ ((one_le_div htot_pos).mpr hq_tot)
        have hrat2 : ((2 : ℝ) ^ j * (D : ℝ)) ^ 2 ≤ (q : ℝ) ^ 2 :=
          pow_le_pow_left₀ h2j_pos.le hq_ge 2
        have h1 : (q : ℝ) / (q.totient : ℝ) ≤
            ((q : ℝ) / (q.totient : ℝ)) * ((D : ℝ) / (q.totient : ℝ)) ^ 2 :=
          le_mul_of_one_le_right (by positivity) hrat1
        have h2 : ((q : ℝ) / (q.totient : ℝ)) * ((D : ℝ) / (q.totient : ℝ)) ^ 2 =
            ((D : ℝ) ^ 2 / ((q : ℝ) ^ 2)) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 := by
          field_simp [hq_pos.ne', htot_pos.ne']
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos h2j_pos) hrat2) (by positivity))
      have hsubB : B j ⊆ Finset.Icc 1 (2 ^ (j + 1) * D) := fun q hq =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1; omega,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2⟩
      calc ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ))
          ≤ ∑ q ∈ B j, ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 2)) * ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
            Finset.sum_le_sum hpt
        _ = ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 2)) * ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 2)) *
              ∑ q ∈ Finset.Icc 1 (2 ^ (j + 1) * D), ((q : ℝ) / (q.totient : ℝ)) ^ 3 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun _ _ _ => by positivity) (by positivity)
        _ ≤ ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 2)) *
              (Real.exp ((2 : ℝ) ^ 3) * ((2 ^ (j + 1) * D : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_div_totient_pow_le 3 _) (by positivity)
        _ = (2 * Real.exp 8 * (D : ℝ)) * ((1 / 2 : ℝ) ^ j) := by
            have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have h2_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
            push_cast
            rw [show (2 : ℝ) ^ 3 = 8 by norm_num, one_div_pow, pow_succ]
            field_simp [hD_ne, h2_ne]; ring
    have hgeom : ∑ j ∈ Finset.range J, ((1 / 2 : ℝ) ^ j) ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ J := by positivity
      have heq : ((1 / 2 : ℝ) ^ J - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ J) := by ring
      linarith
    calc ∑ q ∈ A.filter (fun q => ¬ q ≤ D), ((q : ℝ) / (q.totient : ℝ))
        ≤ ∑ q ∈ (Finset.range J).biUnion B, ((q : ℝ) / (q.totient : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ ≤ ∑ j ∈ Finset.range J, ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ)) :=
          sum_biUnion_le_sum (Finset.range J) B fun _ => by positivity
      _ ≤ ∑ j ∈ Finset.range J, (2 * Real.exp 8 * (D : ℝ)) * ((1 / 2 : ℝ) ^ j) :=
          Finset.sum_le_sum fun j _ => hblock j
      _ = (2 * Real.exp 8 * (D : ℝ)) * ∑ j ∈ Finset.range J, ((1 / 2 : ℝ) ^ j) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * Real.exp 8 * (D : ℝ)) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 4 * Real.exp 8 * (D : ℝ) := by ring
  linarith

/-- Totient cardinality count: `# {q ∈ Icc 1 Q : φ(q) ≤ D} ≤ (exp 2 + 4 * exp 8) * D`. -/
lemma card_totient_le_le (Q D : ℕ) (hD : 1 ≤ D) :
    (((Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)).card : ℝ) ≤
      (Real.exp 2 + 4 * Real.exp 8) * (D : ℝ) := by
  have h1 : (((Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)).card : ℝ) ≤
      ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D), ((q : ℝ) / (q.totient : ℝ)) := by
    calc (((Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)).card : ℝ)
        = ∑ _q ∈ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D), (1 : ℝ) := by simp
      _ ≤ ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D), ((q : ℝ) / (q.totient : ℝ)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
          rw [one_le_div (Nat.cast_pos.mpr (Nat.totient_pos.mpr hq1))]
          exact Nat.cast_le.mpr (Nat.totient_le q)
  exact h1.trans (sum_div_totient_of_totient_le Q D hD)

/-- Inverse-totient cube tail (for `(S+)`):
`∑_{q ∈ Icc 1 Q, D < φ(q)} 1 / φ(q)³ ≤ 4 * (exp 2 + 4 * exp 8) / D²`. -/
theorem sum_inv_totient_cube_of_totient_gt (Q D : ℕ) (hD : 1 ≤ D) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => D < q.totient), (1 : ℝ) / ((q.totient : ℝ) ^ 3) ≤
      4 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2) := by
  let J := Q + 1
  let B : ℕ → Finset ℕ := fun j =>
    (Finset.Icc 1 Q).filter (fun q => 2 ^ j * D < q.totient ∧ q.totient ≤ 2 ^ (j + 1) * D)
  have hcover : (Finset.Icc 1 Q).filter (fun q => D < q.totient) ⊆ (Finset.range J).biUnion B := by
    intro q hq
    have hqIcc := (Finset.mem_filter.mp hq).1
    have hq_leQ := (Finset.mem_Icc.mp hqIcc).2
    have hgt := (Finset.mem_filter.mp hq).2
    let j := Nat.log 2 ((q.totient - 1) / D)
    have hdiv_pos : 1 ≤ (q.totient - 1) / D := (Nat.le_div_iff_mul_le hD).mpr (by omega)
    have hj_lo : 2 ^ j ≤ (q.totient - 1) / D := Nat.pow_log_le_self 2 (by omega)
    have hj_hi : (q.totient - 1) / D < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hj_lt : j < J := by
      have h1 : j < 2 ^ j := Nat.lt_two_pow_self
      have h2 : 2 ^ j ≤ q := hj_lo.trans ((Nat.div_le_self _ _).trans (by have := Nat.totient_le q; omega))
      omega
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt, Finset.mem_filter.mpr ⟨hqIcc, ?_, ?_⟩⟩
    · have := (Nat.le_div_iff_mul_le hD).mp hj_lo; omega
    · have := (Nat.div_lt_iff_lt_mul hD).mp hj_hi; omega
  have hblock : ∀ j : ℕ, ∑ q ∈ B j, (1 : ℝ) / ((q.totient : ℝ) ^ 3) ≤
      (2 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2)) * ((1 / 4 : ℝ) ^ j) := by
    intro j
    have hsub : B j ⊆ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ 2 ^ (j + 1) * D) := fun q hq =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.2⟩
    have hcard : ((B j).card : ℝ) ≤ (Real.exp 2 + 4 * Real.exp 8) * ((2 ^ (j + 1) * D : ℕ) : ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (card_totient_le_le Q (2 ^ (j + 1) * D) (by have : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow; nlinarith))
    have hterm : ∀ q ∈ B j, (1 : ℝ) / ((q.totient : ℝ) ^ 3) ≤ 1 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3) := by
      intro q hq
      have hge : (2 : ℝ) ^ j * (D : ℝ) ≤ (q.totient : ℝ) := by
        have : 2 ^ j * D ≤ q.totient := by have := (Finset.mem_filter.mp hq).2.1; omega
        exact_mod_cast this
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hge 3)
    calc ∑ q ∈ B j, (1 : ℝ) / ((q.totient : ℝ) ^ 3)
        ≤ ∑ _q ∈ B j, (1 : ℝ) / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3) := Finset.sum_le_sum hterm
      _ = ((B j).card : ℝ) * (1 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Real.exp 2 + 4 * Real.exp 8) * ((2 ^ (j + 1) * D : ℕ) : ℝ)) *
            (1 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (2 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2)) * ((1 / 4 : ℝ) ^ j) := by
          have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have h2_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
          have h4_eq : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
          push_cast; rw [one_div_pow, h4_eq, pow_succ]
          field_simp [hD_ne, h2_ne]
  have hgeom : ∑ j ∈ Finset.range J, ((1 / 4 : ℝ) ^ j) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
    have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ J := by positivity
    have heq : ((1 / 4 : ℝ) ^ J - 1) / (1 / 4 - 1) = (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ J) := by ring
    linarith
  calc ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => D < q.totient), (1 : ℝ) / ((q.totient : ℝ) ^ 3)
      ≤ ∑ q ∈ (Finset.range J).biUnion B, (1 : ℝ) / ((q.totient : ℝ) ^ 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
    _ ≤ ∑ j ∈ Finset.range J, ∑ q ∈ B j, (1 : ℝ) / ((q.totient : ℝ) ^ 3) :=
        sum_biUnion_le_sum (Finset.range J) B fun _ => by positivity
    _ ≤ ∑ j ∈ Finset.range J, (2 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2)) * ((1 / 4 : ℝ) ^ j) :=
        Finset.sum_le_sum fun j _ => hblock j
    _ = (2 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2)) * ∑ j ∈ Finset.range J, ((1 / 4 : ℝ) ^ j) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2)) * 2 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 4 * (Real.exp 2 + 4 * Real.exp 8) / ((D : ℝ) ^ 2) := by ring

/-- Logarithmic totient sum (for `(S+)`):
`∑_{q ∈ Icc 1 Q, φ(q) ≤ D} q / φ(q)² ≤ (8 * exp 4 + 8 * exp 16) * log(2 * D)`. -/
theorem sum_div_totient_sq_of_totient_le (Q D : ℕ) (hD : 1 ≤ D) :
    ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
      (8 * Real.exp 4 + 8 * Real.exp 16) * Real.log (2 * (D : ℝ)) := by
  let A := (Finset.Icc 1 Q).filter (fun q => q.totient ≤ D)
  rw [← Finset.sum_filter_add_sum_filter_not A (fun q => q ≤ D)]
  have hlog_ge : (1 : ℝ) / 2 ≤ Real.log (2 * (D : ℝ)) := by
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
        rw [this]; linarith [Real.exp_one_lt_d9]
      have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have := Real.log_le_log (Real.exp_pos _) hexp; rwa [Real.log_exp] at this
    exact hlog2.trans (Real.log_le_log two_pos (by have : (1 : ℝ) ≤ D := Nat.one_le_cast.mpr hD; linarith))
  -- Low range `q ≤ D`: dyadic blocks `2^j ≤ q < 2^(j+1)` with `k = 2`.
  have hlo : ∑ q ∈ A.filter (fun q => q ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
      8 * Real.exp 4 * Real.log (2 * (D : ℝ)) := by
    let K := Nat.log 2 D + 1
    let B : ℕ → Finset ℕ := fun j => Finset.Icc (2 ^ j) (2 ^ (j + 1) - 1)
    have hcover : A.filter (fun q => q ≤ D) ⊆ (Finset.range K).biUnion B := by
      intro q hq
      have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
      have hqD := (Finset.mem_filter.mp hq).2
      let j := Nat.log 2 q
      have hj_lt : j < K := Nat.lt_succ_of_le (Nat.log_mono_right hqD)
      have hj_lo : 2 ^ j ≤ q := Nat.pow_log_le_self 2 (by omega)
      have hj_hi : q < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt, Finset.mem_Icc.mpr ⟨hj_lo, by omega⟩⟩
    have hblock : ∀ j : ℕ, ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤ 2 * Real.exp 4 := by
      intro j
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hpt : ∀ q ∈ B j, (q : ℝ) / ((q.totient : ℝ) ^ 2) ≤ (1 / ((2 : ℝ) ^ j)) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
        intro q hq
        have hq_ge : (2 : ℝ) ^ j ≤ (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hq).1
        have hq_pos : (0 : ℝ) < q := lt_of_lt_of_le h2j_pos hq_ge
        have htot_ne : (q.totient : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (by have := (Finset.mem_Icc.mp hq).1; have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; omega)).ne'
        have heq : (q : ℝ) / ((q.totient : ℝ) ^ 2) = (1 / (q : ℝ)) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := by
          field_simp [hq_pos.ne', htot_ne]
        rw [heq]
        exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le h2j_pos hq_ge) (by positivity)
      have hsubB : B j ⊆ Finset.Icc (1 : ℕ) (2 ^ (j + 1)) := fun q hq =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; have : 1 ≤ 2 ^ j := Nat.one_le_two_pow; omega,
          (Finset.mem_Icc.mp hq).2.trans (Nat.sub_le _ 1)⟩
      calc ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2))
          ≤ ∑ q ∈ B j, (1 / ((2 : ℝ) ^ j)) * ((q : ℝ) / (q.totient : ℝ)) ^ 2 := Finset.sum_le_sum hpt
        _ = (1 / ((2 : ℝ) ^ j)) * ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ)) ^ 2 := (Finset.mul_sum _ _ _).symm
        _ ≤ (1 / ((2 : ℝ) ^ j)) * ∑ q ∈ Finset.Icc (1 : ℕ) (2 ^ (j + 1)), ((q : ℝ) / (q.totient : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun _ _ _ => by positivity) (by positivity)
        _ ≤ (1 / ((2 : ℝ) ^ j)) * (Real.exp ((2 : ℝ) ^ 2) * ((2 ^ (j + 1) : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_div_totient_pow_le 2 _) (by positivity)
        _ = 2 * Real.exp 4 := by
            push_cast; rw [show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ]
            field_simp [h2j_pos.ne']
    have hK_le : (K : ℝ) ≤ 4 * Real.log (2 * (D : ℝ)) := by
      have hpow : (2 : ℝ) ^ (Nat.log 2 D) ≤ (D : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      have hlog : (Nat.log 2 D : ℝ) * Real.log 2 ≤ Real.log (D : ℝ) := by
        have := Real.log_le_log (by positivity) hpow; rwa [Real.log_pow] at this
      have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
        have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
          rw [← Real.exp_nat_mul]
          have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
          rw [this]; linarith [Real.exp_one_lt_d9]
        have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
        have := Real.log_le_log (Real.exp_pos _) hexp; rwa [Real.log_exp] at this
      have hD_pos : (0 : ℝ) < D := Nat.cast_pos.mpr hD
      have hlog_mul : Real.log (2 * (D : ℝ)) = Real.log 2 + Real.log (D : ℝ) :=
        Real.log_mul two_ne_zero hD_pos.ne'
      have hnat_nn : (0 : ℝ) ≤ (Nat.log 2 D : ℝ) := Nat.cast_nonneg _
      have hK_eq : (K : ℝ) = (Nat.log 2 D : ℝ) + 1 := by push_cast [K]; rfl
      nlinarith
    calc ∑ q ∈ A.filter (fun q => q ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2))
        ≤ ∑ q ∈ (Finset.range K).biUnion B, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
      _ ≤ ∑ j ∈ Finset.range K, ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) :=
          sum_biUnion_le_sum (Finset.range K) B fun _ => by positivity
      _ ≤ ∑ _j ∈ Finset.range K, (2 * Real.exp 4) := Finset.sum_le_sum fun j _ => hblock j
      _ = (K : ℝ) * (2 * Real.exp 4) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (4 * Real.log (2 * (D : ℝ))) * (2 * Real.exp 4) := mul_le_mul_of_nonneg_right hK_le (by positivity)
      _ = 8 * Real.exp 4 * Real.log (2 * (D : ℝ)) := by ring
  -- High range `D < q ≤ Q`: dyadic blocks `2^j * D < q ≤ 2^(j+1) * D` with `k = 4` giving `≤ 4 * exp 16 ≤ 8 * exp 16 * log(2D)`.
  have hhi : ∑ q ∈ A.filter (fun q => ¬ q ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
      8 * Real.exp 16 * Real.log (2 * (D : ℝ)) := by
    let J := Q + 1
    let B : ℕ → Finset ℕ := fun j =>
      (Finset.Icc (2 ^ j * D + 1) (2 ^ (j + 1) * D)).filter (fun q => q.totient ≤ D)
    have hcover : A.filter (fun q => ¬ q ≤ D) ⊆ (Finset.range J).biUnion B := by
      intro q hq
      have hq_mem := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
      have hq_leQ := (Finset.mem_Icc.mp hq_mem.1).2
      have hq_tot := hq_mem.2
      have hq_gtD : D < q := by have := (Finset.mem_filter.mp hq).2; omega
      let j := Nat.log 2 ((q - 1) / D)
      have hdiv_pos : 1 ≤ (q - 1) / D := (Nat.le_div_iff_mul_le hD).mpr (by omega)
      have hj_lo : 2 ^ j ≤ (q - 1) / D := Nat.pow_log_le_self 2 (by omega)
      have hj_hi : (q - 1) / D < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hj_lt : j < J := by
        have h1 : j < 2 ^ j := Nat.lt_two_pow_self
        have h2 : 2 ^ j ≤ q := hj_lo.trans ((Nat.div_le_self _ _).trans (by omega))
        omega
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hq_tot⟩⟩
      · have := (Nat.le_div_iff_mul_le hD).mp hj_lo; omega
      · have := (Nat.div_lt_iff_lt_mul hD).mp hj_hi; omega
    have hblock : ∀ j : ℕ, ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤
        (2 * Real.exp 16) * ((1 / 4 : ℝ) ^ j) := by
      intro j
      have h2j_pos : (0 : ℝ) < (2 : ℝ) ^ j * (D : ℝ) := by positivity
      have hpt : ∀ q ∈ B j,
          (q : ℝ) / ((q.totient : ℝ) ^ 2) ≤
            ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) * ((q : ℝ) / (q.totient : ℝ)) ^ 4 := by
        intro q hq
        have hqIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
        have hq_tot : (q.totient : ℝ) ≤ (D : ℝ) := Nat.cast_le.mpr (Finset.mem_filter.mp hq).2
        have hq_ge : (2 : ℝ) ^ j * (D : ℝ) ≤ (q : ℝ) := by
          have : 2 ^ j * D ≤ q := by omega
          exact_mod_cast this
        have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
        have htot_pos : (0 : ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
        have hrat1 : (1 : ℝ) ≤ ((D : ℝ) / (q.totient : ℝ)) ^ 2 :=
          one_le_pow₀ ((one_le_div htot_pos).mpr hq_tot)
        have hrat2 : ((2 : ℝ) ^ j * (D : ℝ)) ^ 3 ≤ (q : ℝ) ^ 3 :=
          pow_le_pow_left₀ h2j_pos.le hq_ge 3
        have h1 : (q : ℝ) / ((q.totient : ℝ) ^ 2) ≤
            ((q : ℝ) / ((q.totient : ℝ) ^ 2)) * ((D : ℝ) / (q.totient : ℝ)) ^ 2 :=
          le_mul_of_one_le_right (by positivity) hrat1
        have h2 : ((q : ℝ) / ((q.totient : ℝ) ^ 2)) * ((D : ℝ) / (q.totient : ℝ)) ^ 2 =
            ((D : ℝ) ^ 2 / ((q : ℝ) ^ 3)) * ((q : ℝ) / (q.totient : ℝ)) ^ 4 := by
          field_simp [hq_pos.ne', htot_pos.ne']
        rw [h2] at h1
        exact h1.trans (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hrat2) (by positivity))
      have hsubB : B j ⊆ Finset.Icc 1 (2 ^ (j + 1) * D) := fun q hq =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1; omega,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2⟩
      calc ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2))
          ≤ ∑ q ∈ B j, ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) * ((q : ℝ) / (q.totient : ℝ)) ^ 4 :=
            Finset.sum_le_sum hpt
        _ = ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) * ∑ q ∈ B j, ((q : ℝ) / (q.totient : ℝ)) ^ 4 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) *
              ∑ q ∈ Finset.Icc 1 (2 ^ (j + 1) * D), ((q : ℝ) / (q.totient : ℝ)) ^ 4 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubB fun _ _ _ => by positivity) (by positivity)
        _ ≤ ((D : ℝ) ^ 2 / (((2 : ℝ) ^ j * (D : ℝ)) ^ 3)) *
              (Real.exp ((2 : ℝ) ^ 4) * ((2 ^ (j + 1) * D : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_div_totient_pow_le 4 _) (by positivity)
        _ = (2 * Real.exp 16) * ((1 / 4 : ℝ) ^ j) := by
            have hD_ne : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have h2_ne : (2 : ℝ) ^ j ≠ 0 := by positivity
            have h4_eq : (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 := by
              rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
            push_cast; rw [show (2 : ℝ) ^ 4 = 16 by norm_num, one_div_pow, h4_eq, pow_succ]
            field_simp [hD_ne, h2_ne]; ring
    have hgeom : ∑ j ∈ Finset.range J, ((1 / 4 : ℝ) ^ j) ≤ 2 := by
      rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1)]
      have hnn : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ J := by positivity
      have heq : ((1 / 4 : ℝ) ^ J - 1) / (1 / 4 - 1) = (4 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ J) := by ring
      linarith
    have hraw : ∑ q ∈ A.filter (fun q => ¬ q ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2)) ≤ 4 * Real.exp 16 := by
      calc ∑ q ∈ A.filter (fun q => ¬ q ≤ D), ((q : ℝ) / ((q.totient : ℝ) ^ 2))
          ≤ ∑ q ∈ (Finset.range J).biUnion B, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) :=
            Finset.sum_le_sum_of_subset_of_nonneg hcover fun _ _ _ => by positivity
        _ ≤ ∑ j ∈ Finset.range J, ∑ q ∈ B j, ((q : ℝ) / ((q.totient : ℝ) ^ 2)) :=
            sum_biUnion_le_sum (Finset.range J) B fun _ => by positivity
        _ ≤ ∑ j ∈ Finset.range J, (2 * Real.exp 16) * ((1 / 4 : ℝ) ^ j) :=
            Finset.sum_le_sum fun j _ => hblock j
        _ = (2 * Real.exp 16) * ∑ j ∈ Finset.range J, ((1 / 4 : ℝ) ^ j) := (Finset.mul_sum _ _ _).symm
        _ ≤ (2 * Real.exp 16) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = 4 * Real.exp 16 := by ring
    have hlog_mul : 4 * Real.exp 16 ≤ 8 * Real.exp 16 * Real.log (2 * (D : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hlog_ge (show (0 : ℝ) ≤ 8 * Real.exp 16 by positivity)
      linarith
    linarith
  linarith

end ArithmeticMoments

end FareyGoldbach
