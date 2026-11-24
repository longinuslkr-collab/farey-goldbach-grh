import FareyGoldbach.Defs
import FareyGoldbach.CharacterBound
import FareyGoldbach.SingularSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log

/-!
# Modules B0 & Supporting Prime-Sum / Arithmetic Estimates

This module proves:
1. **Module B0 (`primePowerMass_le`, `nonCoprimeVonMangoldt_le`)**:
   - `∑_{n ∈ Icc 1 Y} |Λ(n) - primeWeight(n)| ≤ √Y * log Y`.
   - `∑_{n ∈ Icc 1 Y, ¬ Coprime n M} Λ(n) ≤ 2 * log(2M) * log Y`.
2. **Elementary Arithmetic Bounds (zero Mertens / PNT)**:
   - `totient_ratio_le`: `m / φ(m) ≤ 2^256 * m^(1/8)`.
   - `sum_sqfree_div_totient_le`: `∑_{q ∈ Icc 1 Q₀, Squarefree q} q / φ(q) ≤ 3 * Q₀`.
   - `sum_coprime_inv_totient_le`: for `1 ≤ r ≤ Y`, `Q₀ ≤ Y`, `Y ≥ 2^72`,
     `∑_{q ∈ Icc 1 Q₀, Coprime q r, Squarefree q} 1 / φ(q) ≤ 18 * (φ(r)/r) * log(2Y)`.
3. **Quartic Bump & Smoothed Kernel Decay**:
   - `quarticBump_lipschitz`: `|w(x) - w(y)| ≤ 8 * |x - y|`.
   - `norm_sum_e_le`: for `0 < |β| ≤ 1/2`, `‖∑_{j < M} e(β * j)‖ ≤ 1 / (2 * |β|)`.
   - `smoothedKernel_bound_triv` & `smoothedKernel_bound_decay`:
     `‖smoothedKernel r b Y β‖ ≤ min (Y/r + 1) (2 / |β|)`.
4. **Finite Orthogonality & Parseval on `[0, 1]`**:
   - `integral_e_int`, `integral_norm_sq_trigPoly`, `smoothedKernel_l2_le`.
5. **Principal Character Formula (`charCoeff_one_coprime`)**:
   - For `Coprime q r`: `e(-a*b/(rq)) * charCoeff r q a b 1 = e(-a * rInv r q * b / q) * μ(q) / (φ(r) * φ(q))`.
6. **L² Bound for `smoothedPrimeSum` (`smoothedPrimeSum_l2_le`)** from `SmoothedTwistEstimate`.
-/

open scoped BigOperators

namespace FareyGoldbach

section PrimePowerMass

/-- Sum of `Λ(p^k)` over `k ∈ Icc a (Nat.log p Y)` (`1 ≤ a`) is at most `log Y`. -/
lemma sum_log_prime_pow_le_of_pos {p Y a : ℕ} (hp : p.Prime) (hY : 1 ≤ Y) (ha : 1 ≤ a) :
    ∑ _k ∈ Finset.Icc a (Nat.log p Y), Real.log (p : ℝ) ≤ Real.log (Y : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.Icc a (Nat.log p Y)).card ≤ Nat.log p Y := by
    simp only [Nat.card_Icc]
    omega
  have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hp.one_lt.le)
  calc ((Finset.Icc a (Nat.log p Y)).card : ℝ) * Real.log (p : ℝ)
      ≤ (Nat.log p Y : ℝ) * Real.log (p : ℝ) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hlogp_nn
    _ = Real.log (((p ^ Nat.log p Y : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
    _ ≤ Real.log (Y : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast pow_pos hp.pos (Nat.log p Y)
        · exact_mod_cast Nat.pow_log_le_self p (by omega : Y ≠ 0)

lemma primeWeight_le_vonMangoldt (n : ℕ) : primeWeight n ≤ ArithmeticFunction.vonMangoldt n := by
  unfold primeWeight
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h]
  · exact ArithmeticFunction.vonMangoldt_nonneg

lemma primeWeight_nonneg (n : ℕ) : 0 ≤ primeWeight n := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_nonneg (Nat.one_le_cast.mpr h.one_lt.le)
  · rfl

lemma primeWeight_le_log {n Y : ℕ} (hn : n ≤ Y) : primeWeight n ≤ Real.log (Y : ℝ) := by
  unfold primeWeight
  split_ifs with h
  · exact Real.log_le_log (Nat.cast_pos.mpr h.pos) (Nat.cast_le.mpr hn)
  · by_cases hY : 1 ≤ Y
    · exact Real.log_nonneg (Nat.one_le_cast.mpr hY)
    · have : Y = 0 := by omega
      subst this; simp

/-- **Module B0a:** Higher prime powers contribute at most `√Y * log Y`. -/
theorem primePowerMass_le (Y : ℕ) (hY : 1 ≤ Y) :
    ∑ n ∈ Finset.Icc 1 Y, |ArithmeticFunction.vonMangoldt n - primeWeight n| ≤
      Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := by
  classical
  let bad := (Finset.Icc 1 Y).filter fun n => ¬ n.Prime ∧ IsPrimePow n
  have hsum_bad : ∑ n ∈ Finset.Icc 1 Y, |ArithmeticFunction.vonMangoldt n - primeWeight n| =
      ∑ n ∈ bad, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hp, primeWeight, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · by_cases hpp : IsPrimePow n
      · simp [hp, hpp, primeWeight, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      · simp [hp, hpp, primeWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
  rw [hsum_bad]
  let P := (Finset.Icc 1 (Nat.sqrt Y)).filter Nat.Prime
  let pairs := P.sigma fun p => Finset.Icc 2 (Nat.log p Y)
  have hsub : bad ⊆ pairs.image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hn_le : n ≤ Y := (Finset.mem_Icc.mp hmem.1).2
    have hnotp : ¬ n.Prime := hmem.2.1
    obtain ⟨p, k, hp_nat, hk_pos, hpk⟩ := (isPrimePow_nat_iff n).1 hmem.2.2
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have hk1 : k = 1 := by omega
      subst hk1
      simp only [pow_one] at hpk
      exact hnotp (hpk ▸ hp_nat)
    have hp_sq : p * p ≤ Y := by
      calc p * p = p ^ 2 := (sq p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp_nat.pos hk2
        _ = n := hpk
        _ ≤ Y := hn_le
    have hp_le_sqrt : p ≤ Nat.sqrt Y := Nat.le_sqrt.2 hp_sq
    have hk_le_log : k ≤ Nat.log p Y := Nat.le_log_of_pow_le hp_nat.one_lt (hpk.symm ▸ hn_le)
    refine Finset.mem_image.mpr ⟨⟨p, k⟩, ?_, hpk⟩
    exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_nat.pos, hp_le_sqrt⟩, hp_nat⟩,
      Finset.mem_Icc.mpr ⟨hk2, hk_le_log⟩⟩
  calc ∑ n ∈ bad, ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ pairs.image (fun pk => pk.1 ^ pk.2), ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ pk ∈ pairs, ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) :=
        Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ p ∈ P, ∑ k ∈ Finset.Icc 2 (Nat.log p Y), ArithmeticFunction.vonMangoldt (p ^ k) :=
        Finset.sum_sigma _ _ _
    _ = ∑ p ∈ P, ∑ _k ∈ Finset.Icc 2 (Nat.log p Y), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hprime : p.Prime := (Finset.mem_filter.mp hp).2
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkpos : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        rw [ArithmeticFunction.vonMangoldt_apply_pow hkpos,
            ArithmeticFunction.vonMangoldt_apply_prime hprime]
    _ ≤ ∑ _p ∈ P, Real.log (Y : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact sum_log_prime_pow_le_of_pos (Finset.mem_filter.mp hp).2 hY (by omega)
    _ = (P.card : ℝ) * Real.log (Y : ℝ) := by simp [nsmul_eq_mul]
    _ ≤ Real.sqrt (Y : ℝ) * Real.log (Y : ℝ) := by
        have hP_card : P.card ≤ Nat.sqrt Y := by
          calc P.card ≤ (Finset.Icc 1 (Nat.sqrt Y)).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ = Nat.sqrt Y := by simp
        have hsqrt_le : (Nat.sqrt Y : ℝ) ≤ Real.sqrt (Y : ℝ) := by
          rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
          exact_mod_cast (by simpa [sq] using Nat.sqrt_le Y)
        have hlog_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hY)
        exact mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr hP_card).trans hsqrt_le) hlog_nn

/-- Elementary bound `M.primeFactors.card ≤ 2 * log (2 * M)` for `M ≥ 1`. -/
lemma primeFactors_card_le_two_log {M : ℕ} (hM : 1 ≤ M) :
    (M.primeFactors.card : ℝ) ≤ 2 * Real.log (2 * (M : ℝ)) := by
  have h2pow : 2 ^ M.primeFactors.card ≤ M := by
    calc 2 ^ M.primeFactors.card = ∏ _p ∈ M.primeFactors, 2 := by simp
      _ ≤ ∏ p ∈ M.primeFactors, p :=
          Finset.prod_le_prod fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
      _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hexp : Real.exp (1 / 2 : ℝ) ≤ 2 := by
      have hsq : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by
        rw [← Real.exp_nat_mul]
        have : (2 : ℕ) * ((1 : ℝ) / 2) = 1 := by norm_num
        rw [this]
        linarith [Real.exp_one_lt_d9]
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have := Real.log_le_log (Real.exp_pos (1 / 2)) hexp
    rwa [Real.log_exp] at this
  have hlogM : (M.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (M : ℝ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast h2pow)
  have hM_le : Real.log (M : ℝ) ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_le_log (Nat.cast_pos.mpr hM) (by linarith [show (1 : ℝ) ≤ M by exact_mod_cast hM])
  nlinarith

/-- **Module B0b:** Prime powers sharing a prime factor with `M` contribute `≤ 2 * log(2M) * log Y`. -/
theorem nonCoprimeVonMangoldt_le (Y M : ℕ) (hY : 1 ≤ Y) (hM : 1 ≤ M) :
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n M),
      ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log (2 * (M : ℝ)) * Real.log (Y : ℝ) := by
  classical
  let bad := (Finset.Icc 1 Y).filter fun n => ¬ Nat.Coprime n M ∧ IsPrimePow n
  have hsum_bad : ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n M),
      ArithmeticFunction.vonMangoldt n = ∑ n ∈ bad, ArithmeticFunction.vonMangoldt n := by
    have h1 : ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n M),
        ArithmeticFunction.vonMangoldt n =
      ∑ n ∈ ((Finset.Icc 1 Y).filter (fun n => ¬ Nat.Coprime n M)).filter IsPrimePow,
        ArithmeticFunction.vonMangoldt n := by
      symm
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hpp : IsPrimePow n
      · simp [hpp]
      · simp [hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.2 hpp]
    rw [h1]
    congr 1
    ext n
    simp [bad, and_assoc]
  rw [hsum_bad]
  let pairs := M.primeFactors.sigma fun p => Finset.Icc 1 (Nat.log p Y)
  have hsub : bad ⊆ pairs.image (fun pk => pk.1 ^ pk.2) := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hn_le : n ≤ Y := (Finset.mem_Icc.mp hmem.1).2
    obtain ⟨p, k, hp_nat, hk_pos, hpk⟩ := (isPrimePow_nat_iff n).1 hmem.2.2
    have hp_dvd : p ∣ M := by
      by_contra hndvd
      have hcop_p : Nat.Coprime p M := hp_nat.coprime_iff_not_dvd.2 hndvd
      have hcop_pk : Nat.Coprime (p ^ k) M := hcop_p.pow_left k
      exact hmem.2.1 (hpk ▸ hcop_pk)
    have hk_le_log : k ≤ Nat.log p Y := Nat.le_log_of_pow_le hp_nat.one_lt (hpk.symm ▸ hn_le)
    refine Finset.mem_image.mpr ⟨⟨p, k⟩, ?_, hpk⟩
    exact Finset.mem_sigma.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp_nat, hp_dvd, by omega⟩,
      Finset.mem_Icc.mpr ⟨hk_pos, hk_le_log⟩⟩
  calc ∑ n ∈ bad, ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ pairs.image (fun pk => pk.1 ^ pk.2), ArithmeticFunction.vonMangoldt n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ pk ∈ pairs, ArithmeticFunction.vonMangoldt (pk.1 ^ pk.2) :=
        Finset.sum_image_le_of_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
    _ = ∑ p ∈ M.primeFactors, ∑ k ∈ Finset.Icc 1 (Nat.log p Y), ArithmeticFunction.vonMangoldt (p ^ k) :=
        Finset.sum_sigma _ _ _
    _ = ∑ p ∈ M.primeFactors, ∑ _k ∈ Finset.Icc 1 (Nat.log p Y), Real.log (p : ℝ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkpos : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        rw [ArithmeticFunction.vonMangoldt_apply_pow hkpos,
            ArithmeticFunction.vonMangoldt_apply_prime hprime]
    _ ≤ ∑ _p ∈ M.primeFactors, Real.log (Y : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact sum_log_prime_pow_le_of_pos (Nat.prime_of_mem_primeFactors hp) hY (by omega)
    _ = (M.primeFactors.card : ℝ) * Real.log (Y : ℝ) := by simp [nsmul_eq_mul]
    _ ≤ 2 * Real.log (2 * (M : ℝ)) * Real.log (Y : ℝ) := by
        have hlog_nn : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hY)
        exact mul_le_mul_of_nonneg_right (primeFactors_card_le_two_log hM) hlog_nn

end PrimePowerMass

section ElementaryArithmetic

/-- Elementary Bernoulli inequality: `∏_{i ∈ S} (1 - a i) ≥ 1 - ∑_{i ∈ S} a i` for `a i ∈ [0, 1]`. -/
lemma one_sub_sum_le_prod_one_sub {ι : Type*} [DecidableEq ι] (S : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ S, 0 ≤ a i) (ha1 : ∀ i ∈ S, a i ≤ 1) :
    1 - ∑ i ∈ S, a i ≤ ∏ i ∈ S, (1 - a i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self _ _)
    have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self _ _)
    have hs_ih := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    have hsum_nn : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg fun i hi => ha0 i (Finset.mem_insert_of_mem hi)
    have hmul : (1 - a x) * (1 - ∑ i ∈ s, a i) ≤ (1 - a x) * ∏ i ∈ s, (1 - a i) :=
      mul_le_mul_of_nonneg_left hs_ih (by linarith)
    nlinarith

/-- For `m ≥ 1`, `m / φ(m) = ∏_{p ∈ m.primeFactors} (p / (p - 1))`. -/
lemma div_totient_eq_prod (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) =
      ∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have htot := Nat.totient_eq_mul_prod_factors m
  have htot_pos : (0 : ℝ) < m.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm)
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hQ : ((m.totient : ℚ) : ℝ) = (m.totient : ℝ) := by push_cast; rfl
  have htotR : (m.totient : ℝ) = (m : ℝ) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) := by
    have h := congrArg (fun q : ℚ => (q : ℝ)) htot
    simpa [Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_inv] using h
  have hprod_eq : ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp_prime.two_le
    field_simp [(by linarith : (p : ℝ) ≠ 0), (by linarith : (p : ℝ) - 1 ≠ 0)]
  rw [htotR, hprod_eq]
  have hinv_ne : (∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_ne_zero (by linarith) (by linarith)
  field_simp [hm_pos.ne', hinv_ne]

/-- Elementary sub-polynomial bound: `m / φ(m) ≤ 2^16 * m^(1/4)` for all `m ≥ 1`. -/
lemma div_totient_le_rpow_quarter (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) ≤ (2 : ℝ) ^ 16 * (m : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [div_totient_eq_prod m hm]
  set P := m.primeFactors
  set P1 := P.filter (fun p => p < 16)
  set P2 := P.filter (fun p => ¬ (p < 16))
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 16)]
  have h1 : ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (2 : ℝ) ^ 16 := by
    have hcard : P1.card ≤ 16 := by
      have hsub : P1 ⊆ Finset.range 16 := fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ P1, (2 : ℝ) := by
          refine real_prod_le_prod P1 _ _ (fun p hp => ?_) (fun p hp => ?_)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            exact div_nonneg (by linarith) (by linarith)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            rw [div_le_iff₀ (by linarith)]; linarith
      _ = (2 : ℝ) ^ P1.card := by simp
      _ ≤ (2 : ℝ) ^ 16 := pow_le_pow_right₀ (by norm_num) hcard
  have h2 : ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4 : (∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ 4 ≤ (m : ℝ) := by
      rw [← Finset.prod_pow]
      calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ^ 4
          ≤ ∏ p ∈ P2, (p : ℝ) := by
            refine real_prod_le_prod P2 _ _ (fun p hp => ?_) (fun p hp => ?_)
            · have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              exact pow_nonneg (div_nonneg (by linarith) (by linarith)) 4
            · have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              have hle2 : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
                rw [div_le_iff₀ (by linarith)]; linarith
              calc ((p : ℝ) / ((p : ℝ) - 1)) ^ 4 ≤ (2 : ℝ) ^ 4 :=
                    pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hle2 4
                _ = 16 := by norm_num
                _ ≤ (p : ℝ) := hp16
        _ = ((∏ p ∈ P2, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
        _ ≤ (m : ℝ) := by
            exact_mod_cast Nat.le_of_dvd hm
              ((Finset.prod_dvd_prod_of_subset P2 P id (Finset.filter_subset _ _)).trans
                (Nat.prod_primeFactors_dvd m))
    have hnn : 0 ≤ ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) :=
      Finset.prod_nonneg fun p hp => by
        have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
        exact div_nonneg (by linarith) (by linarith)
    calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))
        = ((∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
          norm_num
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (pow_nonneg hnn 4) h4 (by norm_num)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp => by
    have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
    exact div_nonneg (by linarith) (by linarith)) (by positivity)

/-- Elementary sub-polynomial bound with exponent `1/8`: `m / φ(m) ≤ 2^128 * m^(1/8)`. -/
lemma div_totient_le_rpow_eighth (m : ℕ) (hm : 0 < m) :
    (m : ℝ) / (m.totient : ℝ) ≤ ((2 : ℝ) ^ 64) ^ 2 * (m : ℝ) ^ ((1 : ℝ) / 8) := by
  rw [div_totient_eq_prod m hm]
  set P := m.primeFactors
  set P1 := P.filter (fun p => p < 128)
  set P2 := P.filter (fun p => ¬ (p < 128))
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 128)]
  have h1 : ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1)) ≤ ((2 : ℝ) ^ 64) ^ 2 := by
    have hcard : P1.card ≤ 128 := by
      have hsub : P1 ⊆ Finset.range 128 := fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∏ p ∈ P1, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ ∏ _p ∈ P1, (2 : ℝ) := by
          refine real_prod_le_prod P1 _ _ (fun p hp => ?_) (fun p hp => ?_)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            exact div_nonneg (by linarith) (by linarith)
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).two_le
            rw [div_le_iff₀ (by linarith)]; linarith
      _ = (2 : ℝ) ^ P1.card := by simp
      _ ≤ (2 : ℝ) ^ (64 * 2) := pow_le_pow_right₀ (by norm_num) hcard
      _ = ((2 : ℝ) ^ 64) ^ 2 := by rw [pow_mul]
  have h2 : ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ≤ (m : ℝ) ^ ((1 : ℝ) / 8) := by
    have h8 : (∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ 8 ≤ (m : ℝ) := by
      rw [← Finset.prod_pow]
      calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) ^ 8
          ≤ ∏ p ∈ P2, (p : ℝ) := by
            refine real_prod_le_prod P2 _ _ (fun p hp => ?_) (fun p hp => ?_)
            · have hp128 : (128 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              exact pow_nonneg (div_nonneg (by linarith) (by linarith)) 8
            · have hp128 : (128 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
              have hle : (p : ℝ) / ((p : ℝ) - 1) ≤ (128 : ℝ) / 127 := by
                rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
              calc ((p : ℝ) / ((p : ℝ) - 1)) ^ 8 ≤ ((128 : ℝ) / 127) ^ 8 :=
                    pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hle 8
                _ ≤ 128 := by norm_num
                _ ≤ (p : ℝ) := hp128
        _ = ((∏ p ∈ P2, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
        _ ≤ (m : ℝ) := by
            exact_mod_cast Nat.le_of_dvd hm
              ((Finset.prod_dvd_prod_of_subset P2 P id (Finset.filter_subset _ _)).trans
                (Nat.prod_primeFactors_dvd m))
    have hnn : 0 ≤ ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1)) :=
      Finset.prod_nonneg fun p hp => by
        have hp128 : (128 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
        exact div_nonneg (by linarith) (by linarith)
    calc ∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))
        = ((∏ p ∈ P2, ((p : ℝ) / ((p : ℝ) - 1))) ^ (8 : ℕ)) ^ ((1 : ℝ) / 8) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
          norm_num
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 8) := Real.rpow_le_rpow (pow_nonneg hnn 8) h8 (by norm_num)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp => by
    have hp128 : (128 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
    exact div_nonneg (by linarith) (by linarith)) (by positivity)

/-- Prime factors of a product of distinct primes equal the set of primes itself. -/
lemma primeFactors_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, p).primeFactors = T := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hp_prime : p.Prime := hT p (Finset.mem_insert_self _ _)
    have hs_prime : ∀ x ∈ s, x.Prime := fun x hx => hT x (Finset.mem_insert_of_mem hx)
    have hs_ne : ∏ x ∈ s, x ≠ 0 := (Finset.prod_pos fun x hx => (hs_prime x hx).pos).ne'
    rw [Finset.prod_insert hp, Nat.primeFactors_mul hp_prime.ne_zero hs_ne,
        hp_prime.primeFactors, ih hs_prime]
    ext x; simp

/-- For squarefree `q ≥ 1`, `q / φ(q) = ∑_{d ∣ q} 1 / φ(d)`. -/
lemma sqfree_div_totient_eq_sum_divisors {q : ℕ} (hq : 0 < q) (hsf : Squarefree q) :
    (q : ℝ) / (q.totient : ℝ) = ∑ d ∈ q.divisors, (1 / (d.totient : ℝ)) := by
  rw [div_totient_eq_prod q hq]
  have hstep : ∏ p ∈ q.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) =
      ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
    field_simp [(by linarith : (p : ℝ) - 1 ≠ 0)]
    ring
  rw [hstep]
  have hexp : ∏ p ∈ q.primeFactors, (1 + 1 / ((p : ℝ) - 1)) =
      ∑ T ∈ q.primeFactors.powerset, ∏ p ∈ T, (1 / ((p : ℝ) - 1)) := by
    have h := Finset.prod_add (f := fun p : ℕ => 1 / ((p : ℝ) - 1)) (g := fun _ => (1 : ℝ)) q.primeFactors
    simpa [add_comm] using h
  rw [hexp]
  refine Finset.sum_bij (fun T _ => ∏ p ∈ T, p) ?_ ?_ ?_ ?_
  · intro T hT
    have hTsub : T ⊆ q.primeFactors := Finset.mem_powerset.mp hT
    exact Nat.mem_divisors.mpr
      ⟨(Finset.prod_dvd_prod_of_subset T q.primeFactors id hTsub).trans (Nat.prod_primeFactors_dvd q), hq.ne'⟩
  · intro T₁ hT₁ T₂ hT₂ hEq
    have hsub1 := Finset.mem_powerset.mp hT₁
    have hsub2 := Finset.mem_powerset.mp hT₂
    have h1 := primeFactors_prod_primes (fun p hp => Nat.prime_of_mem_primeFactors (hsub1 hp))
    have h2 := primeFactors_prod_primes (fun p hp => Nat.prime_of_mem_primeFactors (hsub2 hp))
    rw [← h1, ← h2, hEq]
  · intro d hd
    have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
    have hd_sf : Squarefree d := hsf.squarefree_of_dvd hdvd
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
    have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sf
    have hsub : d.primeFactors ⊆ q.primeFactors := Nat.primeFactors_mono hdvd hq.ne'
    exact ⟨d.primeFactors, Finset.mem_powerset.mpr hsub, hprod⟩
  · intro T hT
    have hTsub := Finset.mem_powerset.mp hT
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTsub hp)
    have htot : (∏ p ∈ T, p).totient = ∏ p ∈ T, (p - 1) := by
      clear hT hTsub
      induction T using Finset.induction_on with
      | empty => simp
      | @insert p s hp ih =>
        rw [Finset.prod_insert hp, Finset.prod_insert hp]
        have hp_prime : p.Prime := hTprime p (Finset.mem_insert_self _ _)
        have hs_prime : ∀ x ∈ s, x.Prime := fun x hx => hTprime x (Finset.mem_insert_of_mem hx)
        have hcop : Nat.Coprime p (∏ x ∈ s, x) := Nat.Coprime.prod_right fun x hx =>
          (Nat.coprime_primes hp_prime (hs_prime x hx)).2 (fun h => hp (h ▸ hx))
        rw [Nat.totient_mul hcop, Nat.totient_prime hp_prime, ih hs_prime]
    rw [htot, Nat.cast_prod]
    simp_rw [one_div]
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (hTprime p hp).one_lt.le
    rw [Nat.cast_sub hp1, Nat.cast_one]

/-- Telescoping bound: `∑_{k ∈ Icc 2 N} 1 / (k * (k - 1)) ≤ 1`. -/
lemma sum_inv_mul_pred_le_one (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) ≤ 1 := by
  induction N with
  | zero => simp
  | succ m ih =>
    by_cases hm : m < 1
    · have : m = 0 := by omega
      subst this; simp
    · have hm1 : 1 ≤ m := by omega
      have hsplit : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : m + 1 ∉ Finset.Icc 2 m := by simp
      -- Actually prove exact formula `1 - 1 / N` for `N ≥ 1`!
      have hexact : ∀ n : ℕ, 1 ≤ n →
          ∑ k ∈ Finset.Icc 2 n, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (n : ℝ) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => simp
        | succ r hr ihr =>
          have hsp : Finset.Icc 2 (r + 1) = insert (r + 1) (Finset.Icc 2 r) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsp, Finset.sum_insert (by simp), ihr]
          have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
          push_cast
          field_simp [hrpos.ne', (by linarith : (r : ℝ) + 1 ≠ 0)]
          ring
      rw [hexact (m + 1) (by omega)]
      have : (0 : ℝ) < (m + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
      linarith [div_pos one_pos this]

/-- Convergence bound: `∑_{d ∈ Icc 1 N, Squarefree d} 1 / (d * φ(d)) ≤ 3`. -/
lemma sum_sqfree_inv_mul_totient_le_three (N : ℕ) :
    ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ)) ≤ 3 := by
  let S := (Finset.Icc 1 N).filter Nat.Prime
  have h1 : ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ)) ≤
      ∑ T ∈ S.powerset, ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hmap : ∀ d ∈ (Finset.Icc 1 N).filter Squarefree,
        d.primeFactors ∈ S.powerset ∧
        (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ)) =
          ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      intro d hd
      have hd_Icc := (Finset.mem_filter.mp hd).1
      have hd_sf := (Finset.mem_filter.mp hd).2
      have hd_pos : 0 < d := (Finset.mem_Icc.mp hd_Icc).1
      have hd_le : d ≤ N := (Finset.mem_Icc.mp hd_Icc).2
      refine ⟨Finset.mem_powerset.mpr fun p hp => ?_, ?_⟩
      · have hpm := Nat.mem_primeFactors.mp hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpm.1.pos, (Nat.le_of_dvd hd_pos hpm.2.1).trans hd_le⟩, hpm.1⟩
      · have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sf
        have htot : d.totient = ∏ p ∈ d.primeFactors, (p - 1) := by
          have hgen : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (∏ p ∈ T, p).totient = ∏ p ∈ T, (p - 1) := by
            intro T hTprime
            induction T using Finset.induction_on with
            | empty => simp
            | @insert p s hp ih =>
              rw [Finset.prod_insert hp, Finset.prod_insert hp]
              have hp_prime := hTprime p (Finset.mem_insert_self _ _)
              have hs_prime : ∀ x ∈ s, x.Prime := fun x hx => hTprime x (Finset.mem_insert_of_mem hx)
              have hcop : Nat.Coprime p (∏ x ∈ s, x) := Nat.Coprime.prod_right fun x hx =>
                (Nat.coprime_primes hp_prime (hs_prime x hx)).2 (fun h => hp (h ▸ hx))
              rw [Nat.totient_mul hcop, Nat.totient_prime hp_prime, ih hs_prime]
          have h1 := hgen d.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
          rwa [hprod] at h1
        have h1 : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by rw [← Nat.cast_prod, hprod]
        have h2 : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
          rw [htot, Nat.cast_prod]
          refine Finset.prod_congr rfl fun p hp => ?_
          rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
        rw [h1, h2, ← Finset.prod_mul_distrib]
        simp_rw [one_div]
        rw [← Finset.prod_inv_distrib]
    calc ∑ d ∈ (Finset.Icc 1 N).filter Squarefree, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ))
        = ∑ d ∈ (Finset.Icc 1 N).filter Squarefree,
            ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
          Finset.sum_congr rfl fun d hd => (hmap d hd).2
      _ = ∑ T ∈ ((Finset.Icc 1 N).filter Squarefree).image Nat.primeFactors,
            ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          symm
          refine Finset.sum_image fun d₁ hd₁ d₂ hd₂ hEq => ?_
          have h1' := Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₁).2
          have h2' := Nat.prod_primeFactors_of_squarefree (Finset.mem_filter.mp hd₂).2
          rw [← h1', ← h2', hEq]
      _ ≤ ∑ T ∈ S.powerset, ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun T hT _ =>
            Finset.prod_nonneg fun p hp => ?_
          · intro T hT
            obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hT
            exact (hmap d hd).1
          · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Finset.mem_filter.mp (Finset.mem_powerset.mp hT hp)).2.two_le
            exact div_nonneg zero_le_one (by nlinarith)
  have hexp : ∑ T ∈ S.powerset, ∏ p ∈ T, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) =
      ∏ p ∈ S, (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    have h := Finset.prod_add (f := fun p : ℕ => (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
      (g := fun _ => (1 : ℝ)) S
    simpa [add_comm] using h.symm
  have hprod_le : ∏ p ∈ S, (1 + (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤
      Real.exp (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [Real.exp_sum]
    refine real_prod_le_prod S _ _ (fun p hp => ?_) (fun p _ => ?_)
    · have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Finset.mem_filter.mp hp).2.two_le
      have : (0 : ℝ) ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := div_nonneg zero_le_one (by nlinarith)
      linarith
    · linarith [Real.add_one_le_exp ((1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))]
  have hS_sub : S ⊆ Finset.Icc 2 N := fun p hp => by
    have hmem := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hmem.2.two_le, (Finset.mem_Icc.mp hmem.1).2⟩
  have hsum_le : ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
    calc ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ k ∈ Finset.Icc 2 N, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS_sub fun k hk _ => by
            have hk2 : (2 : ℝ) ≤ k := Nat.cast_le.mpr (Finset.mem_Icc.mp hk).1
            exact div_nonneg zero_le_one (by nlinarith)
      _ ≤ 1 := sum_inv_mul_pred_le_one N
  have hexp1 : Real.exp (∑ p ∈ S, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 3 :=
    (Real.exp_le_exp.mpr hsum_le).trans (by linarith [Real.exp_one_lt_d9])
  linarith [h1, hexp, hprod_le, hexp1]

/-- **Elementary sum bound for cell completion:**
`∑_{q ∈ Icc 1 Q₀, Squarefree q} q / φ(q) ≤ 3 * Q₀`. -/
theorem sum_sqfree_div_totient_le (Q₀ : ℕ) :
    ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ((q : ℝ) / (q.totient : ℝ)) ≤ 3 * (Q₀ : ℝ) := by
  classical
  have hrew : ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ((q : ℝ) / (q.totient : ℝ)) =
      ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    exact sqfree_div_totient_eq_sum_divisors (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      (Finset.mem_filter.mp hq).2
  rw [hrew]
  -- Swap sum: each squarefree `d ≤ Q₀` divides at most `Q₀ / d` values of `q ≤ Q₀`.
  have hswap : ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ) ≤
      ∑ d ∈ (Finset.Icc 1 Q₀).filter Squarefree,
        ((Q₀ / d : ℕ) : ℝ) * ((1 : ℝ) / (d.totient : ℝ)) := by
    let Qsf := (Finset.Icc 1 Q₀).filter Squarefree
    calc ∑ q ∈ Qsf, ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ)
        = ∑ q ∈ Qsf, ∑ d ∈ Qsf, (if d ∣ q then (1 : ℝ) / (d.totient : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ fun _ _ => rfl
          ext d
          simp only [Qsf, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
          have hq2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).2
          have hqsf := (Finset.mem_filter.mp hq).2
          constructor
          · rintro ⟨hdvd, _⟩
            exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdvd hq1, (Nat.le_of_dvd hq1 hdvd).trans hq2⟩,
              hqsf.squarefree_of_dvd hdvd⟩, hdvd⟩
          · rintro ⟨_, hdvd⟩
            exact ⟨hdvd, by omega⟩
      _ = ∑ d ∈ Qsf, ∑ q ∈ Qsf, (if d ∣ q then (1 : ℝ) / (d.totient : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ Qsf, ((Qsf.filter (fun q => d ∣ q)).card : ℝ) * ((1 : ℝ) / (d.totient : ℝ)) := by
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ d ∈ Qsf, ((Q₀ / d : ℕ) : ℝ) * ((1 : ℝ) / (d.totient : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          have hcard : (Qsf.filter (fun q => d ∣ q)).card ≤ Q₀ / d := by
            have hsub : Qsf.filter (fun q => d ∣ q) ⊆ (Finset.Icc 1 (Q₀ / d)).image (fun m => d * m) := by
              intro q hq
              have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
              have hq2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2
              obtain ⟨m, rfl⟩ := (Finset.mem_filter.mp hq).2
              refine Finset.mem_image.mpr ⟨m, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
              · exact Nat.pos_of_mul_pos_left hq1
              · exact (Nat.le_div_iff_mul_le hd_pos).2 (by simpa [mul_comm] using hq2)
            exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (by positivity)
  calc ∑ q ∈ (Finset.Icc 1 Q₀).filter Squarefree, ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ)
      ≤ ∑ d ∈ (Finset.Icc 1 Q₀).filter Squarefree, ((Q₀ / d : ℕ) : ℝ) * ((1 : ℝ) / (d.totient : ℝ)) := hswap
    _ ≤ ∑ d ∈ (Finset.Icc 1 Q₀).filter Squarefree,
          ((Q₀ : ℝ) / (d : ℝ)) * ((1 : ℝ) / (d.totient : ℝ)) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
        have hdiv_le : ((Q₀ / d : ℕ) : ℝ) ≤ (Q₀ : ℝ) / (d : ℝ) := by
          rw [le_div_iff₀ hd_pos]
          exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Q₀ d)
        exact mul_le_mul_of_nonneg_right hdiv_le (by positivity)
    _ = (Q₀ : ℝ) * ∑ d ∈ (Finset.Icc 1 Q₀).filter Squarefree, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ (Q₀ : ℝ) * 3 := mul_le_mul_of_nonneg_left (sum_sqfree_inv_mul_totient_le_three Q₀) (Nat.cast_nonneg _)
    _ = 3 * (Q₀ : ℝ) := by ring

/-- Elementary harmonic bound: `∑_{n ∈ Icc 1 M} 1 / n ≤ 1 + log M` for `M ≥ 1`. -/
lemma harmonic_le_one_add_log {M : ℕ} (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hsp : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsp, Finset.sum_insert (by simp)]
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hk1_pos : (0 : ℝ) < (k + 1 : ℕ) := Nat.cast_pos.mpr (by omega)
    have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      have hexp : 1 - 1 / ((k + 1 : ℕ) : ℝ) ≤ Real.exp (-(1 / ((k + 1 : ℕ) : ℝ))) := by
        linarith [Real.add_one_le_exp (-(1 / ((k + 1 : ℕ) : ℝ)))]
      have hfrac : 1 - 1 / ((k + 1 : ℕ) : ℝ) = (k : ℝ) / ((k + 1 : ℕ) : ℝ) := by
        push_cast; field_simp [(by linarith : (k : ℝ) + 1 ≠ 0)]; ring
      rw [hfrac] at hexp
      have hlog := Real.log_le_log (div_pos hk_pos hk1_pos) hexp
      rw [Real.log_div hk_pos.ne' hk1_pos.ne', Real.log_exp] at hlog
      linarith
    linarith

/-- Elementary product bound `∏_{p ∈ r.primeFactors} (1 + 1 / √p) ≤ 2^16 * r^(1/4)`. -/
lemma prod_one_add_inv_sqrt_le (r : ℕ) (hr : 0 < r) :
    ∏ p ∈ r.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) ≤ (2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4) := by
  set P := r.primeFactors
  set P1 := P.filter (fun p => p < 16)
  set P2 := P.filter (fun p => ¬ (p < 16))
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p < 16)]
  have h1 : ∏ p ∈ P1, (1 + 1 / Real.sqrt (p : ℝ)) ≤ (2 : ℝ) ^ 16 := by
    have hcard : P1.card ≤ 16 := by
      have hsub : P1 ⊆ Finset.range 16 := fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      exact (Finset.card_le_card hsub).trans (by simp)
    calc ∏ p ∈ P1, (1 + 1 / Real.sqrt (p : ℝ))
        ≤ ∏ _p ∈ P1, (2 : ℝ) := by
          refine real_prod_le_prod P1 _ _ (fun _ _ => by positivity) (fun p hp => ?_)
          have hp1 : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos
          have hsq : (1 : ℝ) ≤ Real.sqrt (p : ℝ) := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hp1
          have hinv : 1 / Real.sqrt (p : ℝ) ≤ 1 := div_le_one_of_le₀ hsq (by positivity)
          linarith
      _ = (2 : ℝ) ^ P1.card := by simp
      _ ≤ (2 : ℝ) ^ 16 := pow_le_pow_right₀ (by norm_num) hcard
  have h2 : ∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ)) ≤ (r : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4 : (∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ))) ^ 4 ≤ (r : ℝ) := by
      rw [← Finset.prod_pow]
      calc ∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ)) ^ 4
          ≤ ∏ p ∈ P2, (p : ℝ) := by
            refine real_prod_le_prod P2 _ _ (fun _ _ => by positivity) (fun p hp => ?_)
            have hp16 : (16 : ℝ) ≤ p := Nat.cast_le.mpr (not_lt.mp (Finset.mem_filter.mp hp).2)
            have hsq4 : (4 : ℝ) ≤ Real.sqrt (p : ℝ) := by
              rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
            have hinv : 1 / Real.sqrt (p : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq4
            calc (1 + 1 / Real.sqrt (p : ℝ)) ^ 4 ≤ ((5 : ℝ) / 4) ^ 4 :=
                  pow_le_pow_left₀ (by positivity) (by linarith) 4
              _ ≤ 16 := by norm_num
              _ ≤ (p : ℝ) := hp16
        _ = ((∏ p ∈ P2, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
        _ ≤ (r : ℝ) := by
            exact_mod_cast Nat.le_of_dvd hr
              ((Finset.prod_dvd_prod_of_subset P2 P id (Finset.filter_subset _ _)).trans
                (Nat.prod_primeFactors_dvd r))
    have hnn : 0 ≤ ∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ)) :=
      Finset.prod_nonneg fun _ _ => by positivity
    calc ∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ))
        = ((∏ p ∈ P2, (1 + 1 / Real.sqrt (p : ℝ))) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]; norm_num
      _ ≤ (r : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (pow_nonneg hnn 4) h4 (by norm_num)
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => by positivity) (by positivity)

/-- **Elementary harmonic coprime bound (zero Mertens):**
For `1 ≤ r ≤ Y`, `Q₀ ≤ Y`, and `2 ^ 72 ≤ Y`,
`∑_{m ∈ Icc 1 Q₀, Coprime m r} 1 / m ≤ 6 * (φ(r) / r) * log(2 * Y)`. -/
lemma sum_coprime_inv_le {r Q₀ Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hQY : Q₀ ≤ Y)
    (hY_large : 2 ^ 72 ≤ Y) :
    ∑ m ∈ (Finset.Icc 1 Q₀).filter (fun m => Nat.Coprime m r), (1 : ℝ) / (m : ℝ) ≤
      6 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
  classical
  -- Construct the finite set `S_r` of `r`-smooth integers with exponent `≤ K = 4 * r`.
  let P := r.primeFactors
  let K : ℕ := 4 * r
  let eval : (P → Fin (K + 1)) → ℕ := fun f => ∏ p : P, (p : ℕ) ^ (f p).val
  have heval_pos : ∀ f, 0 < eval f := fun f =>
    Finset.prod_pos fun p _ => pow_pos (Nat.prime_of_mem_primeFactors p.2).pos _
  have heval_inj : Function.Injective eval := by
    intro f₁ f₂ hEq
    funext p
    have hfac := congrArg (fun n => n.factorization (p : ℕ)) hEq
    have hcalc : ∀ f : P → Fin (K + 1), (eval f).factorization (p : ℕ) = (f p).val := by
      intro f
      change (∏ q ∈ (Finset.univ : Finset P), (q : ℕ) ^ (f q).val).factorization (p : ℕ) = (f p).val
      rw [Nat.factorization_prod (fun q _ => pow_ne_zero _ (Nat.prime_of_mem_primeFactors q.2).ne_zero)]
      have hsum_apply : ∀ (s : Finset P) (g : P → ℕ →₀ ℕ) (x : ℕ),
          (∑ q ∈ s, g q) x = ∑ q ∈ s, g q x := by
        intro s g x
        induction s using Finset.induction_on with
        | empty => simp
        | @insert a t ha _ => simp [Finset.sum_insert ha]
      rw [hsum_apply]
      rw [Finset.sum_eq_single p]
      · rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors p.2), Finsupp.single_eq_same]
      · intro q _ hqp
        rw [Nat.Prime.factorization_pow (Nat.prime_of_mem_primeFactors q.2), Finsupp.single_eq_of_ne]
        intro hval
        exact hqp (Subtype.ext hval.symm)
      · intro hp; exact absurd (Finset.mem_univ p) hp
    rw [hcalc f₁, hcalc f₂] at hfac
    exact Fin.ext hfac
  let S_r : Finset ℕ := (Finset.univ : Finset (P → Fin (K + 1))).image eval
  have hS_r_pf : ∀ d ∈ S_r, d.primeFactors ⊆ P ∧ 0 < d := by
    intro d hd
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hd
    refine ⟨?_, heval_pos f⟩
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hdvd : q ∣ ∏ p : P, (p : ℕ) ^ (f p).val := Nat.dvd_of_mem_primeFactors hq
    have hprime_dvd_prod : ∀ (s : Finset P) (g : P → ℕ), q ∣ ∏ p ∈ s, g p → ∃ p ∈ s, q ∣ g p := by
      intro s g h
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.prod_empty] at h
        exact absurd (Nat.dvd_one.mp h) hqp.ne_one
      | @insert a t ha ih =>
        rw [Finset.prod_insert ha] at h
        rcases hqp.dvd_mul.mp h with h1 | h2
        · exact ⟨a, Finset.mem_insert_self _ _, h1⟩
        · obtain ⟨p, hp, hdp⟩ := ih h2
          exact ⟨p, Finset.mem_insert_of_mem hp, hdp⟩
    obtain ⟨p, _, hp_dvd⟩ := hprime_dvd_prod Finset.univ (fun p : P => (p : ℕ) ^ (f p).val) hdvd
    have hqp_eq : q = (p : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq hqp (Nat.prime_of_mem_primeFactors p.2)).1
        (hqp.prime.dvd_of_dvd_pow hp_dvd)
    exact hqp_eq ▸ p.2
  -- Step 1: Total sum `∑_{d ∈ S_r} 1 / d ≥ (3 / 4) * (r / φ(r))`.
  have htotal : (3 / 4 : ℝ) * ((r : ℝ) / (r.totient : ℝ)) ≤ ∑ d ∈ S_r, (1 : ℝ) / (d : ℝ) := by
    have hsum_prod : ∑ d ∈ S_r, (1 : ℝ) / (d : ℝ) =
        ∏ p : P, ∑ e : Fin (K + 1), (1 / (p : ℝ)) ^ e.val := by
      rw [Finset.sum_image (fun f₁ _ f₂ _ h => heval_inj h)]
      have h1 : ∀ f : P → Fin (K + 1), (1 : ℝ) / ((eval f : ℕ) : ℝ) =
          ∏ p : P, (1 / (p : ℝ)) ^ (f p).val := by
        intro f
        simp only [eval, Nat.cast_prod, Nat.cast_pow, one_div, Finset.prod_inv_distrib, inv_pow]
      simp_rw [h1]
      exact (Fintype.prod_sum fun (p : P) (e : Fin (K + 1)) => (1 / (p : ℝ)) ^ e.val).symm
    rw [hsum_prod, div_totient_eq_prod r hr, ← Finset.prod_coe_sort P]
    have hfactor : ∀ p : P,
        (1 - 1 / (4 * (r : ℝ))) * ((p : ℝ) / ((p : ℝ) - 1)) ≤
          ∑ e : Fin (K + 1), (1 / (p : ℝ)) ^ e.val := by
      intro p
      have hp_prime := Nat.prime_of_mem_primeFactors p.2
      have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp_prime.two_le
      rw [Fin.sum_univ_eq_sum_range (fun k => (1 / (p : ℝ)) ^ k) (K + 1)]
      have hne : (1 / (p : ℝ)) ≠ 1 := by
        intro h; have : (p : ℝ) = 1 := by field_simp [(by linarith : (p : ℝ) ≠ 0)] at h; linarith
        linarith
      rw [geom_sum_eq hne]
      have hpow_le : (1 / (p : ℝ)) ^ (K + 1) ≤ 1 / (4 * (r : ℝ)) := by
        have h2K : 4 * r ≤ 2 ^ (K + 1) := by
          have := Nat.lt_two_pow_self (n := K + 1)
          omega
        have hpK : (4 * r : ℕ) ≤ (p : ℕ) ^ (K + 1) :=
          h2K.trans (Nat.pow_le_pow_left hp_prime.two_le (K + 1))
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpK)
      have hLHS : ((1 / (p : ℝ)) ^ (K + 1) - 1) / (1 / (p : ℝ) - 1) =
          (1 - (1 / (p : ℝ)) ^ (K + 1)) * ((p : ℝ) / ((p : ℝ) - 1)) := by
        have h1p : 1 / (p : ℝ) - 1 = -(((p : ℝ) - 1) / (p : ℝ)) := by
          field_simp [(by linarith : (p : ℝ) ≠ 0)]; ring
        rw [h1p, div_neg, div_div_eq_mul_div]
        ring
      rw [hLHS]
      exact mul_le_mul_of_nonneg_right (by linarith) (div_nonneg (by linarith) (by linarith))
    calc (3 / 4 : ℝ) * ∏ p : P, ((p : ℝ) / ((p : ℝ) - 1))
        ≤ (∏ _p : P, (1 - 1 / (4 * (r : ℝ)))) * ∏ p : P, ((p : ℝ) / ((p : ℝ) - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun p _ => by
            have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors p.2).two_le
            exact div_nonneg (by linarith) (by linarith))
          have hbern := one_sub_sum_le_prod_one_sub (Finset.univ : Finset P)
            (fun _ => 1 / (4 * (r : ℝ)))
            (fun _ _ => by positivity)
            (fun _ _ => by
              rw [div_le_one (by positivity)]
              have : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
              linarith)
          have hcard_le : P.card ≤ r := by
            calc P.card ≤ (Finset.Icc 1 r).card := Finset.card_le_card fun p hp =>
                  Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
                    Nat.le_of_dvd hr (Nat.dvd_of_mem_primeFactors hp)⟩
              _ = r := by simp
          have hsum_le : ∑ _p : P, (1 : ℝ) / (4 * (r : ℝ)) ≤ 1 / 4 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            have : (P.card : ℝ) ≤ r := Nat.cast_le.mpr hcard_le
            linarith
          linarith
      _ = ∏ p : P, ((1 - 1 / (4 * (r : ℝ))) * ((p : ℝ) / ((p : ℝ) - 1))) := by
          rw [← Finset.prod_mul_distrib]
      _ ≤ ∏ p : P, ∑ e : Fin (K + 1), (1 / (p : ℝ)) ^ e.val := by
          refine real_prod_le_prod Finset.univ _ _ (fun p _ => ?_) (fun p _ => hfactor p)
          have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors p.2).two_le
          have hr1 : (1 : ℝ) ≤ r := Nat.one_le_cast.mpr hr
          have h1 : (0 : ℝ) ≤ 1 - 1 / (4 * (r : ℝ)) := by
            have : 1 / (4 * (r : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
            linarith
          exact mul_nonneg h1 (div_nonneg (by linarith) (by linarith))
  -- Step 2: Tail `S_gt = {d ∈ S_r | Y < d}` has sum `≤ (1 / 4) * (r / φ(r))`.
  let S_le := S_r.filter (fun d => d ≤ Y)
  let S_gt := S_r.filter (fun d => ¬ (d ≤ Y))
  have htail : ∑ d ∈ S_gt, (1 : ℝ) / (d : ℝ) ≤ (1 / 4 : ℝ) * ((r : ℝ) / (r.totient : ℝ)) := by
    have hY_pos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
    have hrankin : ∑ d ∈ S_gt, (1 : ℝ) / (d : ℝ) ≤
        (1 / Real.sqrt (Y : ℝ)) * ∑ d ∈ S_r, (1 : ℝ) / Real.sqrt (d : ℝ) := by
      rw [Finset.mul_sum]
      calc ∑ d ∈ S_gt, (1 : ℝ) / (d : ℝ)
          ≤ ∑ d ∈ S_gt, (1 / Real.sqrt (Y : ℝ)) * ((1 : ℝ) / Real.sqrt (d : ℝ)) := by
            refine Finset.sum_le_sum fun d hd => ?_
            have hgt : Y < d := not_le.mp (Finset.mem_filter.mp hd).2
            have hsqY : Real.sqrt (Y : ℝ) ≤ Real.sqrt (d : ℝ) :=
              Real.sqrt_le_sqrt (Nat.cast_le.mpr hgt.le)
            have hsqd_pos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
            have hsqY_pos : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.mpr hY_pos
            have hmul_eq : (d : ℝ) = Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) :=
              (Real.mul_self_sqrt (Nat.cast_nonneg d)).symm
            rw [one_div_mul_one_div, one_div_le_one_div (by exact_mod_cast (by omega : 0 < d)) (mul_pos hsqY_pos hsqd_pos)]
            conv_rhs => rw [hmul_eq]
            exact mul_le_mul_of_nonneg_right hsqY hsqd_pos.le
        _ ≤ ∑ d ∈ S_r, (1 / Real.sqrt (Y : ℝ)) * ((1 : ℝ) / Real.sqrt (d : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => by positivity
    have hsum_sqrt : ∑ d ∈ S_r, (1 : ℝ) / Real.sqrt (d : ℝ) ≤
        ((r : ℝ) / (r.totient : ℝ)) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4)) := by
      have hsp : ∑ d ∈ S_r, (1 : ℝ) / Real.sqrt (d : ℝ) =
          ∏ p : P, ∑ e : Fin (K + 1), (1 / Real.sqrt (p : ℝ)) ^ e.val := by
        rw [Finset.sum_image (fun f₁ _ f₂ _ h => heval_inj h)]
        have h1 : ∀ f : P → Fin (K + 1), (1 : ℝ) / Real.sqrt ((eval f : ℕ) : ℝ) =
            ∏ p : P, (1 / Real.sqrt (p : ℝ)) ^ (f p).val := by
          intro f
          simp only [eval, Nat.cast_prod, Nat.cast_pow]
          rw [Real.sqrt_prod _ fun _ _ => by positivity, one_div, ← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun p _ => ?_
          have hsqrt_pow : ∀ (x : ℝ) (n : ℕ), 0 ≤ x → Real.sqrt (x ^ n) = (Real.sqrt x) ^ n := by
            intro x n hx
            induction n with
            | zero => simp
            | succ k ih => rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih]
          rw [hsqrt_pow (p : ℝ) (f p).val (Nat.cast_nonneg _), one_div, inv_pow]
        simp_rw [h1]
        exact (Fintype.prod_sum fun (p : P) (e : Fin (K + 1)) => (1 / Real.sqrt (p : ℝ)) ^ e.val).symm
      rw [hsp, div_totient_eq_prod r hr]
      calc ∏ p : P, ∑ e : Fin (K + 1), (1 / Real.sqrt (p : ℝ)) ^ e.val
          ≤ ∏ p : P, (((p : ℝ) / ((p : ℝ) - 1)) * (1 + 1 / Real.sqrt (p : ℝ))) := by
            refine real_prod_le_prod Finset.univ _ _
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (fun p _ => ?_)
            have hp_prime := Nat.prime_of_mem_primeFactors p.2
            have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hp_prime.two_le
            have hsqp_gt : (1 : ℝ) < Real.sqrt (p : ℝ) := by
              rw [Real.lt_sqrt (by norm_num)]; linarith
            rw [Fin.sum_univ_eq_sum_range (fun k => (1 / Real.sqrt (p : ℝ)) ^ k) (K + 1)]
            have hlt1 : 1 / Real.sqrt (p : ℝ) < 1 := (div_lt_one (by linarith)).2 hsqp_gt
            rw [geom_sum_eq hlt1.ne]
            have hle_inf : ((1 / Real.sqrt (p : ℝ)) ^ (K + 1) - 1) / (1 / Real.sqrt (p : ℝ) - 1) ≤
                1 / (1 - 1 / Real.sqrt (p : ℝ)) := by
              have hden : 0 < 1 - 1 / Real.sqrt (p : ℝ) := by linarith
              have hrew : ((1 / Real.sqrt (p : ℝ)) ^ (K + 1) - 1) / (1 / Real.sqrt (p : ℝ) - 1) =
                  (1 - (1 / Real.sqrt (p : ℝ)) ^ (K + 1)) / (1 - 1 / Real.sqrt (p : ℝ)) := by
                have hneg : 1 / Real.sqrt (p : ℝ) - 1 = -(1 - 1 / Real.sqrt (p : ℝ)) := by ring
                rw [hneg, div_neg, ← neg_div, neg_sub]
              rw [hrew]
              exact div_le_div_of_nonneg_right (by linarith [pow_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (p : ℝ)) (K + 1)]) hden.le
            have hid : 1 / (1 - 1 / Real.sqrt (p : ℝ)) =
                ((p : ℝ) / ((p : ℝ) - 1)) * (1 + 1 / Real.sqrt (p : ℝ)) := by
              have hsq : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) := Real.mul_self_sqrt (by linarith)
              have hden1 : 1 - 1 / Real.sqrt (p : ℝ) ≠ 0 := by linarith
              field_simp [hden1, (by linarith : (p : ℝ) - 1 ≠ 0), (by linarith : Real.sqrt (p : ℝ) ≠ 0)]
              nlinarith [hsq]
            exact hle_inf.trans hid.le
        _ = (∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) * ∏ p ∈ P, (1 + 1 / Real.sqrt (p : ℝ)) := by
            rw [Finset.prod_mul_distrib,
                Finset.prod_coe_sort P (fun p => (p : ℝ) / ((p : ℝ) - 1)),
                Finset.prod_coe_sort P (fun p => 1 + 1 / Real.sqrt (p : ℝ))]
        _ ≤ (∏ p ∈ P, ((p : ℝ) / ((p : ℝ) - 1))) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4)) := by
            refine mul_le_mul_of_nonneg_left (prod_one_add_inv_sqrt_le r hr) ?_
            exact Finset.prod_nonneg fun p hp => by
              have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr (Nat.prime_of_mem_primeFactors hp).two_le
              exact div_nonneg (by linarith) (by linarith)
    have hcoeff : (1 / Real.sqrt (Y : ℝ)) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4)) ≤ 1 / 4 := by
      have hrY_R : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
      have hrpow : (r : ℝ) ^ ((1 : ℝ) / 4) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hrY_R (by norm_num)
      have hsq_rpow : Real.sqrt (Y : ℝ) = (Y : ℝ) ^ ((1 : ℝ) / 4) * (Y : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hY_pos]; norm_num
      have hY18 : ((2 : ℝ) ^ 18) ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) := by
        have h72 : ((2 : ℝ) ^ 18) ^ (4 : ℕ) ≤ (Y : ℝ) := by
          have : ((2 : ℝ) ^ 18) ^ (4 : ℕ) = ((2 ^ 72 : ℕ) : ℝ) := by push_cast; ring
          rw [this]
          exact Nat.cast_le.mpr hY_large
        calc (2 : ℝ) ^ 18 = (((2 : ℝ) ^ 18) ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) := by
              rw [← Real.rpow_natCast ((2 : ℝ) ^ 18) 4, ← Real.rpow_mul (by positivity)]; norm_num
          _ ≤ (Y : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) h72 (by norm_num)
      have hY4_pos : 0 < (Y : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hY_pos _
      rw [hsq_rpow]
      calc (1 / ((Y : ℝ) ^ ((1 : ℝ) / 4) * (Y : ℝ) ^ ((1 : ℝ) / 4))) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4))
          ≤ (1 / ((Y : ℝ) ^ ((1 : ℝ) / 4) * (Y : ℝ) ^ ((1 : ℝ) / 4))) * ((2 : ℝ) ^ 16 * (Y : ℝ) ^ ((1 : ℝ) / 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow (by positivity)) (by positivity)
        _ = (2 : ℝ) ^ 16 / (Y : ℝ) ^ ((1 : ℝ) / 4) := by field_simp [hY4_pos.ne']
        _ ≤ (2 : ℝ) ^ 16 / (2 : ℝ) ^ 18 := div_le_div_of_nonneg_left (by positivity) (by positivity) hY18
        _ = 1 / 4 := by norm_num
    calc ∑ d ∈ S_gt, (1 : ℝ) / (d : ℝ)
        ≤ (1 / Real.sqrt (Y : ℝ)) * (((r : ℝ) / (r.totient : ℝ)) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4))) :=
          hrankin.trans (mul_le_mul_of_nonneg_left hsum_sqrt (by positivity))
      _ = ((1 / Real.sqrt (Y : ℝ)) * ((2 : ℝ) ^ 16 * (r : ℝ) ^ ((1 : ℝ) / 4))) * ((r : ℝ) / (r.totient : ℝ)) := by ring
      _ ≤ (1 / 4 : ℝ) * ((r : ℝ) / (r.totient : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
  -- Step 3: Subtract tail to get `∑_{d ∈ S_le} 1 / d ≥ (1 / 2) * (r / φ(r))`.
  have hS_le_ge : (1 / 2 : ℝ) * ((r : ℝ) / (r.totient : ℝ)) ≤ ∑ d ∈ S_le, (1 : ℝ) / (d : ℝ) := by
    have hsplit : ∑ d ∈ S_r, (1 : ℝ) / (d : ℝ) =
        ∑ d ∈ S_le, (1 : ℝ) / (d : ℝ) + ∑ d ∈ S_gt, (1 : ℝ) / (d : ℝ) :=
      (Finset.sum_filter_add_sum_filter_not S_r (fun d => d ≤ Y) _).symm
    linarith
  -- Step 4: Multiply `S_le` by `M = {m ∈ Icc 1 Q₀ | Coprime m r}` injectively into `Icc 1 (Y * Y)`.
  let M := (Finset.Icc 1 Q₀).filter (fun m => Nat.Coprime m r)
  have hmul_le : (∑ d ∈ S_le, (1 : ℝ) / (d : ℝ)) * (∑ m ∈ M, (1 : ℝ) / (m : ℝ)) ≤
      ∑ n ∈ Finset.Icc 1 (Y * Y), (1 : ℝ) / (n : ℝ) := by
    rw [Finset.sum_mul_sum]
    have hprod_eq : ∑ d ∈ S_le, ∑ m ∈ M, (1 : ℝ) / (d : ℝ) * ((1 : ℝ) / (m : ℝ)) =
        ∑ dm ∈ S_le.product M, (1 : ℝ) / (((dm.1 * dm.2 : ℕ) : ℝ)) := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun m _ => ?_
      rw [Nat.cast_mul]; ring
    rw [hprod_eq]
    have hinj : Set.InjOn (fun dm : ℕ × ℕ => dm.1 * dm.2) (S_le.product M : Set (ℕ × ℕ)) := by
      rintro ⟨d₁, m₁⟩ h1 ⟨d₂, m₂⟩ h2 hEq
      have hd1 := Finset.mem_filter.mp (Finset.mem_product.mp h1).1
      have hm1 := Finset.mem_filter.mp (Finset.mem_product.mp h1).2
      have hd2 := Finset.mem_filter.mp (Finset.mem_product.mp h2).1
      have hm2 := Finset.mem_filter.mp (Finset.mem_product.mp h2).2
      have hcop12 : Nat.Coprime d₁ m₂ := by
        apply Nat.coprime_of_dvd
        intro p hp hp1 hp2
        have hpP : p ∈ P := (hS_r_pf d₁ hd1.1).1 (Nat.mem_primeFactors.mpr ⟨hp, hp1, (hS_r_pf d₁ hd1.1).2.ne'⟩)
        have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hpP
        have h1' : p ∣ 1 := by
          have := Nat.dvd_gcd hp2 hpr
          rwa [hm2.2.gcd_eq_one] at this
        exact hp.ne_one (Nat.dvd_one.mp h1')
      have hcop21 : Nat.Coprime d₂ m₁ := by
        apply Nat.coprime_of_dvd
        intro p hp hp1 hp2
        have hpP : p ∈ P := (hS_r_pf d₂ hd2.1).1 (Nat.mem_primeFactors.mpr ⟨hp, hp1, (hS_r_pf d₂ hd2.1).2.ne'⟩)
        have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hpP
        have h1' : p ∣ 1 := by
          have := Nat.dvd_gcd hp2 hpr
          rwa [hm1.2.gcd_eq_one] at this
        exact hp.ne_one (Nat.dvd_one.mp h1')
      have hd12 : d₁ ∣ d₂ := hcop12.dvd_of_dvd_mul_right ⟨m₁, by linarith⟩
      have hd21 : d₂ ∣ d₁ := hcop21.dvd_of_dvd_mul_right ⟨m₂, by linarith⟩
      have hd_eq : d₁ = d₂ := Nat.dvd_antisymm hd12 hd21
      have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left (hS_r_pf d₁ hd1.1).2 (hd_eq ▸ hEq)
      exact Prod.ext hd_eq hm_eq
    rw [← Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (g := fun dm : ℕ × ℕ => dm.1 * dm.2)
        (fun a ha b hb h => hinj ha hb h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
    intro n hn
    obtain ⟨⟨d, m⟩, hdm, rfl⟩ := Finset.mem_image.mp hn
    have hd := Finset.mem_filter.mp (Finset.mem_product.mp hdm).1
    have hm := Finset.mem_filter.mp (Finset.mem_product.mp hdm).2
    have hd_pos := (hS_r_pf d hd.1).2
    have hm_pos := (Finset.mem_Icc.mp hm.1).1
    have hm_le : m ≤ Y := (Finset.mem_Icc.mp hm.1).2.trans hQY
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hd_pos hm_pos, Nat.mul_le_mul hd.2 hm_le⟩
  have hharm : ∑ n ∈ Finset.Icc 1 (Y * Y), (1 : ℝ) / (n : ℝ) ≤ 3 * Real.log (2 * (Y : ℝ)) := by
    have hY2_pos : 1 ≤ Y * Y := by nlinarith
    have h1 := harmonic_le_one_add_log hY2_pos
    have hlog2Y : (1 : ℝ) ≤ Real.log (2 * (Y : ℝ)) := by
      have : Real.exp 1 ≤ 2 * (Y : ℝ) := by
        have hY4 : (4 : ℝ) ≤ Y := by
          have : 4 ≤ 2 ^ 72 := by norm_num
          exact_mod_cast this.trans hY_large
        linarith [Real.exp_one_lt_d9]
      have := Real.log_le_log (Real.exp_pos 1) this
      rwa [Real.log_exp] at this
    have hlog_sq : Real.log ((Y * Y : ℕ) : ℝ) ≤ 2 * Real.log (2 * (Y : ℝ)) := by
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast (by omega : Y ≠ 0)) (by exact_mod_cast (by omega : Y ≠ 0))]
      have hle : Real.log (Y : ℝ) ≤ Real.log (2 * (Y : ℝ)) :=
        Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) (by linarith [show (1 : ℝ) ≤ Y by exact_mod_cast (by omega : 1 ≤ Y)])
      linarith
    linarith
  have hM_nn : 0 ≤ ∑ m ∈ M, (1 : ℝ) / (m : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have hcomb : ((1 / 2 : ℝ) * ((r : ℝ) / (r.totient : ℝ))) * (∑ m ∈ M, (1 : ℝ) / (m : ℝ)) ≤
      3 * Real.log (2 * (Y : ℝ)) :=
    (mul_le_mul_of_nonneg_right hS_le_ge hM_nn).trans (hmul_le.trans hharm)
  have hrtot_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) * ((r : ℝ) / (r.totient : ℝ)) := by positivity
  have hdiv := (le_div_iff₀' hpos).2 hcomb
  calc ∑ m ∈ M, (1 : ℝ) / (m : ℝ)
      ≤ 3 * Real.log (2 * (Y : ℝ)) / ((1 / 2 : ℝ) * ((r : ℝ) / (r.totient : ℝ))) := hdiv
    _ = 6 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
        field_simp [hrtot_pos.ne', hr_pos.ne']; ring

/-- **Upgraded L² arithmetic sum bound:**
`∑_{q ∈ Icc 1 Q₀, Coprime q r, Squarefree q} 1 / φ(q) ≤ 18 * (φ(r) / r) * log(2 * Y)`. -/
theorem sum_coprime_inv_totient_le {r Q₀ Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hQY : Q₀ ≤ Y)
    (hY_large : 2 ^ 72 ≤ Y) :
    ∑ q ∈ ((Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)).filter Squarefree,
      (1 : ℝ) / (q.totient : ℝ) ≤
        18 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by
  classical
  let Qset := ((Finset.Icc 1 Q₀).filter (fun q => Nat.Coprime q r)).filter Squarefree
  have hrew : ∑ q ∈ Qset, (1 : ℝ) / (q.totient : ℝ) =
      ∑ q ∈ Qset, (1 / (q : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq_pos : 0 < q := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
    have hq_sf : Squarefree q := (Finset.mem_filter.mp hq).2
    rw [← sqfree_div_totient_eq_sum_divisors hq_pos hq_sf]
    have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
    field_simp [hqR]
  rw [hrew]
  -- Swap sum by writing `q = d * m` with `d` squarefree, `m ≤ Q₀`, `Coprime m r`.
  let Dset := (Finset.Icc 1 Q₀).filter Squarefree
  let Mset := (Finset.Icc 1 Q₀).filter (fun m => Nat.Coprime m r)
  have hle : ∑ q ∈ Qset, (1 / (q : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ) ≤
      (∑ d ∈ Dset, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ))) *
        (∑ m ∈ Mset, (1 : ℝ) / (m : ℝ)) := by
    calc ∑ q ∈ Qset, (1 / (q : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ)
        = ∑ q ∈ Qset, ∑ d ∈ Dset, (if d ∣ q then (1 : ℝ) / ((q : ℝ) * (d.totient : ℝ)) else 0) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          rw [Finset.mul_sum, ← Finset.sum_filter]
          have hq1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).1
          have hq2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2
          have hqsf := (Finset.mem_filter.mp hq).2
          refine Finset.sum_congr ?_ fun d _ => by ring
          ext d
          simp only [Dset, Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨hdvd, _⟩
            exact ⟨⟨⟨Nat.pos_of_dvd_of_pos hdvd hq1, (Nat.le_of_dvd hq1 hdvd).trans hq2⟩,
              hqsf.squarefree_of_dvd hdvd⟩, hdvd⟩
          · rintro ⟨_, hdvd⟩
            exact ⟨hdvd, by omega⟩
      _ = ∑ d ∈ Dset, ∑ q ∈ Qset, (if d ∣ q then (1 : ℝ) / ((q : ℝ) * (d.totient : ℝ)) else 0) :=
          Finset.sum_comm
      _ ≤ ∑ d ∈ Dset, ((1 : ℝ) / ((d : ℝ) * (d.totient : ℝ))) * (∑ m ∈ Mset, (1 : ℝ) / (m : ℝ)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          rw [← Finset.sum_filter, Finset.mul_sum]
          have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          have hsub : (Qset.filter (fun q => d ∣ q)).image (fun q => q / d) ⊆ Mset := by
            intro m hm
            obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hm
            have hq_mem := (Finset.mem_filter.mp hq).1
            have hdvd := (Finset.mem_filter.mp hq).2
            have hq_cop := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem).1).2
            have hq_Icc := (Finset.mem_filter.mp (Finset.mem_filter.mp hq_mem).1).1
            have hq1 := (Finset.mem_Icc.mp hq_Icc).1
            have hq2 := (Finset.mem_Icc.mp hq_Icc).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
            · exact Nat.div_pos (Nat.le_of_dvd hq1 hdvd) hd_pos
            · exact (Nat.div_le_self q d).trans hq2
            · exact hq_cop.coprime_dvd_left (Nat.div_dvd_of_dvd hdvd)
          have hrew2 : ∑ q ∈ Qset.filter (fun q => d ∣ q), (1 : ℝ) / ((q : ℝ) * (d.totient : ℝ)) =
              ∑ m ∈ (Qset.filter (fun q => d ∣ q)).image (fun q => q / d),
                (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ)) * ((1 : ℝ) / (m : ℝ)) := by
            rw [Finset.sum_image]
            · refine Finset.sum_congr rfl fun q hq => ?_
              have hdvd := (Finset.mem_filter.mp hq).2
              have hqeq : (q : ℝ) = (d : ℝ) * ((q / d : ℕ) : ℝ) := by
                exact_mod_cast (Nat.mul_div_cancel' hdvd).symm
              rw [hqeq]; ring
            · intro q₁ hq₁ q₂ hq₂ hEq
              dsimp only at hEq
              have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hq₁).2
              have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hq₂).2
              rw [← h1, ← h2, hEq]
          rw [hrew2]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = (∑ d ∈ Dset, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ))) * (∑ m ∈ Mset, (1 : ℝ) / (m : ℝ)) :=
          (Finset.sum_mul _ _ _).symm
  calc ∑ q ∈ Qset, (1 / (q : ℝ)) * ∑ d ∈ q.divisors, (1 : ℝ) / (d.totient : ℝ)
      ≤ (∑ d ∈ Dset, (1 : ℝ) / ((d : ℝ) * (d.totient : ℝ))) * (∑ m ∈ Mset, (1 : ℝ) / (m : ℝ)) := hle
    _ ≤ 3 * (6 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ))) :=
        mul_le_mul (sum_sqfree_inv_mul_totient_le_three Q₀)
          (sum_coprime_inv_le hr hrY hQY hY_large)
          (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    _ = 18 * ((r.totient : ℝ) / (r : ℝ)) * Real.log (2 * (Y : ℝ)) := by ring

end ElementaryArithmetic

section QuarticAndKernel

/-- Elementary Lipschitz bound `|quarticBump x - quarticBump y| ≤ 8 * |x - y|`. -/
lemma quarticBump_lipschitz (x y : ℝ) : |quarticBump x - quarticBump y| ≤ 8 * |x - y| := by
  have hcore : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      |16 * a ^ 2 * (1 - a) ^ 2 - 16 * b ^ 2 * (1 - b) ^ 2| ≤ 8 * |a - b| := by
    intro a b ha0 ha1 hb0 hb1
    have hfac : 16 * a ^ 2 * (1 - a) ^ 2 - 16 * b ^ 2 * (1 - b) ^ 2 =
        16 * (a * (1 - a) + b * (1 - b)) * (1 - a - b) * (a - b) := by ring
    rw [hfac, abs_mul, abs_mul, abs_mul]
    have h1 : |a * (1 - a) + b * (1 - b)| ≤ 1 / 2 := by
      have ha : 0 ≤ a * (1 - a) ∧ a * (1 - a) ≤ 1 / 4 :=
        ⟨by nlinarith, by nlinarith [sq_nonneg (a - 1 / 2)]⟩
      have hb : 0 ≤ b * (1 - b) ∧ b * (1 - b) ≤ 1 / 4 :=
        ⟨by nlinarith, by nlinarith [sq_nonneg (b - 1 / 2)]⟩
      rw [abs_of_nonneg (by linarith)]; linarith
    have h2 : |1 - a - b| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h16 : |(16 : ℝ)| = 16 := by norm_num
    rw [h16]
    have h12 : 16 * |a * (1 - a) + b * (1 - b)| * |1 - a - b| ≤ 8 := by
      calc 16 * |a * (1 - a) + b * (1 - b)| * |1 - a - b|
          ≤ 16 * (1 / 2) * 1 := by
            have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
            linarith
        _ = 8 := by norm_num
    exact (mul_le_mul_of_nonneg_right h12 (abs_nonneg _))
  have hval : ∀ z : ℝ, quarticBump z = 16 * (max 0 (min 1 z)) ^ 2 * (1 - max 0 (min 1 z)) ^ 2 := by
    intro z
    unfold quarticBump
    split_ifs with h
    · rw [min_eq_right h.2.le, max_eq_right h.1.le]
    · by_cases h0 : z ≤ 0
      · rw [min_eq_right (by linarith), max_eq_left h0]; ring
      · have h1 : 1 ≤ z := by push Not at h; exact h (by linarith)
        rw [min_eq_left h1, max_eq_right (by norm_num)]; ring
  rw [hval x, hval y]
  have hcl : ∀ z : ℝ, 0 ≤ max (0 : ℝ) (min 1 z) ∧ max (0 : ℝ) (min 1 z) ≤ 1 := fun z =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have h1 := hcore _ _ (hcl x).1 (hcl x).2 (hcl y).1 (hcl y).2
  have hlip : |max (0 : ℝ) (min 1 x) - max (0 : ℝ) (min 1 y)| ≤ |x - y| := by
    have h_max : ∀ u v : ℝ, |max (0 : ℝ) u - max (0 : ℝ) v| ≤ |u - v| := fun u v => by
      rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
      · rw [max_eq_right hu, max_eq_right hv]
      · rw [max_eq_right hu, max_eq_left hv, sub_zero, abs_of_nonneg hu, abs_of_nonneg (by linarith)]; linarith
      · rw [max_eq_left hu, max_eq_right hv, zero_sub, abs_neg, abs_of_nonneg hv, abs_of_nonpos (by linarith)]; linarith
      · rw [max_eq_left hu, max_eq_left hv, sub_self, abs_zero]; exact abs_nonneg _
    have h_min : ∀ u v : ℝ, |min (1 : ℝ) u - min (1 : ℝ) v| ≤ |u - v| := fun u v => by
      rcases le_total 1 u with hu | hu <;> rcases le_total 1 v with hv | hv
      · rw [min_eq_left hu, min_eq_left hv, sub_self, abs_zero]; exact abs_nonneg _
      · rw [min_eq_left hu, min_eq_right hv, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [min_eq_right hu, min_eq_left hv, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      · rw [min_eq_right hu, min_eq_right hv]
    exact (h_max _ _).trans (h_min x y)
  exact h1.trans (mul_le_mul_of_nonneg_left hlip (by norm_num))

/-- `quarticBump` is monotone nondecreasing on `(-∞, 1/2]` and nonincreasing on `[1/2, ∞)`. -/
lemma quarticBump_mono_left {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 1 / 2) :
    quarticBump x ≤ quarticBump y := by
  unfold quarticBump
  split_ifs with hx hy'
  · have h1 : x * (1 - x) ≤ y * (1 - y) := by nlinarith
    have h0 : 0 ≤ x * (1 - x) := by nlinarith [hx.1, hx.2]
    nlinarith
  · exfalso; exact hy' ⟨by linarith [hx.1], by linarith⟩
  · positivity
  · rfl

lemma quarticBump_anti_right {x y : ℝ} (hx : 1 / 2 ≤ x) (hxy : x ≤ y) :
    quarticBump y ≤ quarticBump x := by
  unfold quarticBump
  split_ifs with hy hx'
  · have h1 : y * (1 - y) ≤ x * (1 - x) := by nlinarith
    have h0 : 0 ≤ y * (1 - y) := by nlinarith [hy.1, hy.2]
    nlinarith
  · exfalso; exact hx' ⟨by linarith, by linarith [hy.2]⟩
  · positivity
  · rfl

/-- Total variation of `quarticBump` along any monotone sequence is at most `3`. -/
lemma quarticBump_variation_le_three (N : ℕ) (x : ℕ → ℝ) (hmono : ∀ j, x j ≤ x (j + 1)) :
    ∑ j ∈ Finset.range N, |quarticBump (x (j + 1)) - quarticBump (x j)| ≤ 3 := by
  have hmono_le : ∀ a b, a ≤ b → x a ≤ x b := fun a b hab => by
    induction hab with
    | refl => rfl
    | step _ ih => exact ih.trans (hmono _)
  -- Partition `range N` into `A` (`x (j+1) ≤ 1/2`), `B` (`1/2 ≤ x j`), and at most one crossing index `C`.
  let A := (Finset.range N).filter (fun j => x (j + 1) ≤ 1 / 2)
  let B := (Finset.range N).filter (fun j => 1 / 2 < x (j + 1) ∧ 1 / 2 ≤ x j)
  let C := (Finset.range N).filter (fun j => x j < 1 / 2 ∧ 1 / 2 < x (j + 1))
  have hsplit : ∑ j ∈ Finset.range N, |quarticBump (x (j + 1)) - quarticBump (x j)| =
      ∑ j ∈ A, |quarticBump (x (j + 1)) - quarticBump (x j)| +
      ∑ j ∈ B, |quarticBump (x (j + 1)) - quarticBump (x j)| +
      ∑ j ∈ C, |quarticBump (x (j + 1)) - quarticBump (x j)| := by
    have h1 := (Finset.sum_filter_add_sum_filter_not (Finset.range N) (fun j => x (j + 1) ≤ 1 / 2)
      (fun j => |quarticBump (x (j + 1)) - quarticBump (x j)|)).symm
    have h2 := (Finset.sum_filter_add_sum_filter_not
      ((Finset.range N).filter (fun j => ¬ (x (j + 1) ≤ 1 / 2)))
      (fun j => 1 / 2 ≤ x j)
      (fun j => |quarticBump (x (j + 1)) - quarticBump (x j)|)).symm
    have hB : ((Finset.range N).filter (fun j => ¬ (x (j + 1) ≤ 1 / 2))).filter (fun j => 1 / 2 ≤ x j) = B := by
      ext j; simp only [B, Finset.mem_filter, not_le]; tauto
    have hC : ((Finset.range N).filter (fun j => ¬ (x (j + 1) ≤ 1 / 2))).filter (fun j => ¬ (1 / 2 ≤ x j)) = C := by
      ext j; simp only [C, Finset.mem_filter, not_le]; tauto
    rw [hB, hC] at h2
    linarith
  have hA : ∑ j ∈ A, |quarticBump (x (j + 1)) - quarticBump (x j)| ≤ 1 := by
    by_cases hAne : A.Nonempty
    · let m := A.max' hAne
      have hm_mem : m ∈ A := Finset.max'_mem A hAne
      have hA_eq : A = Finset.range (m + 1) := by
        ext j
        simp only [A, Finset.mem_filter, Finset.mem_range]
        constructor
        · intro hj
          exact Nat.lt_succ_of_le (Finset.le_max' A j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj.2⟩))
        · intro hj
          have hm_lt : m < N := Finset.mem_range.mp (Finset.mem_filter.mp hm_mem).1
          have hm_half : x (m + 1) ≤ 1 / 2 := (Finset.mem_filter.mp hm_mem).2
          exact ⟨by omega, (hmono_le (j + 1) (m + 1) (by omega)).trans hm_half⟩
      rw [hA_eq]
      have htele : ∑ j ∈ Finset.range (m + 1), |quarticBump (x (j + 1)) - quarticBump (x j)| =
          quarticBump (x (m + 1)) - quarticBump (x 0) := by
        calc ∑ j ∈ Finset.range (m + 1), |quarticBump (x (j + 1)) - quarticBump (x j)|
            = ∑ j ∈ Finset.range (m + 1), (quarticBump (x (j + 1)) - quarticBump (x j)) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
              have hhalf : x (j + 1) ≤ 1 / 2 :=
                (hmono_le (j + 1) (m + 1) (by omega)).trans (Finset.mem_filter.mp hm_mem).2
              exact abs_of_nonneg (sub_nonneg.mpr (quarticBump_mono_left (hmono j) hhalf))
          _ = quarticBump (x (m + 1)) - quarticBump (x 0) := Finset.sum_range_sub (fun j => quarticBump (x j)) (m + 1)
      rw [htele]
      linarith [quarticBump_le_one (x (m + 1)), quarticBump_nonneg (x 0)]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hAne]; simp
  have hB : ∑ j ∈ B, |quarticBump (x (j + 1)) - quarticBump (x j)| ≤ 1 := by
    by_cases hBne : B.Nonempty
    · let m := B.min' hBne
      let M := B.max' hBne
      have hm_mem : m ∈ B := Finset.min'_mem B hBne
      have hM_mem : M ∈ B := Finset.max'_mem B hBne
      have hmM : m ≤ M := Finset.min'_le B M hM_mem
      have hB_eq : B = Finset.Icc m M := by
        ext j
        simp only [B, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · intro hj
          have hjB : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj.1, hj.2⟩
          exact ⟨Finset.min'_le B j hjB, Finset.le_max' B j hjB⟩
        · rintro ⟨h1, h2⟩
          have hM_lt : M < N := Finset.mem_range.mp (Finset.mem_filter.mp hM_mem).1
          have hm1 : 1 / 2 < x (m + 1) := (Finset.mem_filter.mp hm_mem).2.1
          have hm2 : 1 / 2 ≤ x m := (Finset.mem_filter.mp hm_mem).2.2
          exact ⟨by omega, hm1.trans_le (hmono_le (m + 1) (j + 1) (by omega)), hm2.trans (hmono_le m j h1)⟩
      rw [hB_eq]
      have htele : ∑ j ∈ Finset.Icc m M, |quarticBump (x (j + 1)) - quarticBump (x j)| =
          quarticBump (x m) - quarticBump (x (M + 1)) := by
        calc ∑ j ∈ Finset.Icc m M, |quarticBump (x (j + 1)) - quarticBump (x j)|
            = ∑ j ∈ Finset.Icc m M, (quarticBump (x j) - quarticBump (x (j + 1))) := by
              refine Finset.sum_congr rfl fun j hj => ?_
              have hjm : m ≤ j := (Finset.mem_Icc.mp hj).1
              have hhalf : 1 / 2 ≤ x j := (Finset.mem_filter.mp hm_mem).2.2.trans (hmono_le m j hjm)
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (quarticBump_anti_right hhalf (hmono j)))]
          _ = ∑ k ∈ Finset.range (M + 1 - m), (quarticBump (x (m + k)) - quarticBump (x (m + k + 1))) := by
              refine Finset.sum_bij (fun j _ => j - m) ?_ ?_ ?_ ?_
              · intro j hj; rw [Finset.mem_range]; have := Finset.mem_Icc.mp hj; omega
              · intro j₁ hj₁ j₂ hj₂ h; have := Finset.mem_Icc.mp hj₁; have := Finset.mem_Icc.mp hj₂; omega
              · intro k hk; refine ⟨m + k, Finset.mem_Icc.mpr ⟨by omega, by rw [Finset.mem_range] at hk; omega⟩, by omega⟩
              · intro j hj
                have h1 := (Finset.mem_Icc.mp hj).1
                have hsub : m + (j - m) = j := Nat.add_sub_of_le h1
                rw [hsub]
          _ = quarticBump (x m) - quarticBump (x (M + 1)) := by
              have h := Finset.sum_range_sub' (fun k => quarticBump (x (m + k))) (M + 1 - m)
              have hadd : m + (M + 1 - m) = M + 1 := by omega
              simpa [hadd, add_assoc] using h
      rw [htele]
      linarith [quarticBump_le_one (x m), quarticBump_nonneg (x (M + 1))]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hBne]; simp
  have hC : ∑ j ∈ C, |quarticBump (x (j + 1)) - quarticBump (x j)| ≤ 1 := by
    have hcard : C.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro j₁ hj₁ j₂ hj₂
      have h1 := (Finset.mem_filter.mp hj₁).2
      have h2 := (Finset.mem_filter.mp hj₂).2
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hmono_le (j₁ + 1) j₂ (by omega); linarith
      · have := hmono_le (j₂ + 1) j₁ (by omega); linarith
    calc ∑ j ∈ C, |quarticBump (x (j + 1)) - quarticBump (x j)|
        ≤ ∑ _j ∈ C, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_le]
          constructor <;> linarith [quarticBump_nonneg (x (j + 1)), quarticBump_le_one (x (j + 1)),
            quarticBump_nonneg (x j), quarticBump_le_one (x j)]
      _ = (C.card : ℝ) := by simp
      _ ≤ 1 := by exact_mod_cast hcard
  linarith

/-- Exact chord identity: `‖e x - 1‖ = 2 * |sin (π * x)|`. -/
lemma norm_e_sub_one_eq (x : ℝ) : ‖e x - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hfac : e x - 1 = e (x / 2) * (e (x / 2) - e (-(x / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : x / 2 + x / 2 = x := by ring
    have h2 : x / 2 + -(x / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  rw [hfac, norm_mul, norm_e, one_mul]
  have hsin : e (x / 2) - e (-(x / 2)) = (2 * Real.sin (Real.pi * x) : ℝ) * Complex.I := by
    unfold e
    have h1 : 2 * (Real.pi : ℂ) * ((x / 2 : ℝ) : ℂ) * Complex.I = ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have h2 : 2 * (Real.pi : ℂ) * ((-(x / 2) : ℝ) : ℂ) * Complex.I = -(((Real.pi * x : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [h1, h2]
    conv_rhs => rw [Complex.ofReal_mul, Complex.ofReal_sin]
    have hsin_id : (2 * Complex.I) * Complex.sin ((Real.pi * x : ℝ) : ℂ) =
        Complex.exp (((Real.pi * x : ℝ) : ℂ) * Complex.I) -
          Complex.exp (-(((Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
      rw [Complex.sin]
      have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
      field_simp [hI]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [← hsin_id]
    push_cast; ring
  rw [hsin, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos two_pos]

/-- Elementary chord bound: `‖e x - 1‖ ≤ 2 * π * |x|` for all `x : ℝ`. -/
lemma norm_e_sub_one_le (x : ℝ) : ‖e x - 1‖ ≤ 2 * Real.pi * |x| := by
  rw [norm_e_sub_one_eq]
  have h := Real.abs_sin_le_abs (x := Real.pi * x)
  rw [abs_mul, abs_of_pos Real.pi_pos] at h
  linarith

/-- Lower bound `4 * |β| ≤ ‖e β - 1‖` for `|β| ≤ 1 / 2`. -/
lemma four_mul_abs_le_norm_e_sub_one {β : ℝ} (hβ : |β| ≤ 1 / 2) :
    4 * |β| ≤ ‖e β - 1‖ := by
  rw [norm_e_sub_one_eq]
  have hsin_ge : 2 * |β| ≤ |Real.sin (Real.pi * β)| := by
    have habs : |Real.sin (Real.pi * β)| = Real.sin (Real.pi * |β|) := by
      rcases le_total 0 β with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg]
        apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le h0)
        have : |β| = β := abs_of_nonneg h0
        nlinarith [Real.pi_pos]
      · have hneg : Real.sin (Real.pi * (-β)) = -Real.sin (Real.pi * β) := by
          rw [mul_neg, Real.sin_neg]
        have hnn : 0 ≤ Real.sin (Real.pi * (-β)) := by
          apply Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos])
          have : |β| = -β := abs_of_nonpos h0
          nlinarith [Real.pi_pos]
        rw [abs_of_nonpos h0, abs_of_nonpos (by linarith), hneg]
    rw [habs]
    have hmul := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * |β|) (by nlinarith [Real.pi_pos])
    have h2 : 2 / Real.pi * (Real.pi * |β|) = 2 * |β| := by
      field_simp [Real.pi_pos.ne']
    linarith
  linarith

/-- Geometric sum bound: `‖∑_{j < M} e(β * j)‖ ≤ 1 / (2 * |β|)` for `0 < |β| ≤ 1 / 2`. -/
lemma norm_sum_e_le (M : ℕ) {β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) :
    ‖∑ j ∈ Finset.range M, e (β * (j : ℝ))‖ ≤ 1 / (2 * |β|) := by
  have hpow : ∀ j : ℕ, e (β * (j : ℝ)) = (e β) ^ j := fun j => by
    rw [mul_comm, e_nat_mul]
  simp_rw [hpow]
  have hge := four_mul_abs_le_norm_e_sub_one hβ
  have hne : e β ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hge
    have : 0 < |β| := abs_pos.mpr hβ0
    linarith
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖(e β) ^ M - 1‖ ≤ 2 := by
    calc ‖(e β) ^ M - 1‖ ≤ ‖(e β) ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_pow, norm_e, one_pow, norm_one]
      _ = 2 := by norm_num
  have habs_pos : 0 < |β| := abs_pos.mpr hβ0
  calc ‖(e β) ^ M - 1‖ / ‖e β - 1‖
      ≤ 2 / (4 * |β|) := div_le_div₀ (by norm_num) hnum (by positivity) hge
    _ = 1 / (2 * |β|) := by field_simp [habs_pos.ne']; ring

/-- Trivial bound on `smoothedKernel`: `‖smoothedKernel r b Y β‖ ≤ Y / r + 1`. -/
lemma smoothedKernel_bound_triv (r b Y : ℕ) (β : ℝ) :
    ‖smoothedKernel r b Y β‖ ≤ (Y : ℝ) / (r : ℝ) + 1 := by
  unfold smoothedKernel
  calc ‖∑ j ∈ Finset.range (Y / r + 1), (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ))‖
      ≤ ∑ j ∈ Finset.range (Y / r + 1), ‖(quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ) * e (β * (j : ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range (Y / r + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (quarticBump_nonneg _)]
        exact quarticBump_le_one _
    _ = ((Y / r + 1 : ℕ) : ℝ) := by simp
    _ ≤ (Y : ℝ) / (r : ℝ) + 1 := by
        by_cases hr : r = 0
        · subst hr; simp
        · have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
          have hdiv : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
          push_cast; linarith

/-- Decay bound on `smoothedKernel` via summation by parts:
for `0 < |β| ≤ 1 / 2`, `‖smoothedKernel r b Y β‖ ≤ 2 / |β|`. -/
lemma smoothedKernel_bound_decay (r b Y : ℕ) {β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| ≤ 1 / 2) :
    ‖smoothedKernel r b Y β‖ ≤ 2 / |β| := by
  unfold smoothedKernel
  set N := Y / r + 1
  let w : ℕ → ℝ := fun j => quarticBump ((r * j + b : ℝ) / (Y : ℝ))
  let B : ℕ → ℂ := fun m => ∑ j ∈ Finset.range m, e (β * (j : ℝ))
  have hB_le : ∀ m, ‖B m‖ ≤ 1 / (2 * |β|) := fun m => norm_sum_e_le m hβ0 hβ
  -- Summation by parts: `∑_{j < N} w j * (B (j+1) - B j) = w N * B N - ∑_{j < N} (w (j+1) - w j) * B (j+1)`.
  have hsbp : ∑ j ∈ Finset.range N, (w j : ℂ) * e (β * (j : ℝ)) =
      (w N : ℂ) * B N - ∑ j ∈ Finset.range N, ((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1) := by
    have hstep : ∀ j, (w j : ℂ) * e (β * (j : ℝ)) =
        ((w (j + 1) : ℂ) * B (j + 1) - (w j : ℂ) * B j) -
          ((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1) := by
      intro j
      have hBsucc : B (j + 1) = B j + e (β * (j : ℝ)) := Finset.sum_range_succ _ j
      rw [hBsucc]; push_cast; ring
    simp_rw [hstep]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j => (w j : ℂ) * B j) N]
    simp [B]
  rw [hsbp]
  have hvar : ∑ j ∈ Finset.range N, |w (j + 1) - w j| ≤ 3 := by
    apply quarticBump_variation_le_three N (fun j => (r * j + b : ℝ) / (Y : ℝ))
    intro j
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg Y)
    push_cast
    nlinarith [show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  have habs_pos : 0 < |β| := abs_pos.mpr hβ0
  calc ‖(w N : ℂ) * B N - ∑ j ∈ Finset.range N, ((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1)‖
      ≤ ‖(w N : ℂ) * B N‖ + ‖∑ j ∈ Finset.range N, ((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1)‖ :=
        norm_sub_le _ _
    _ ≤ 1 * (1 / (2 * |β|)) + ∑ j ∈ Finset.range N, |w (j + 1) - w j| * (1 / (2 * |β|)) := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _)]
          exact mul_le_mul (quarticBump_le_one _) (hB_le N) (norm_nonneg _) zero_le_one
        · calc ‖∑ j ∈ Finset.range N, ((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1)‖
              ≤ ∑ j ∈ Finset.range N, ‖((w (j + 1) - w j : ℝ) : ℂ) * B (j + 1)‖ := norm_sum_le _ _
            _ ≤ ∑ j ∈ Finset.range N, |w (j + 1) - w j| * (1 / (2 * |β|)) := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                exact mul_le_mul_of_nonneg_left (hB_le (j + 1)) (abs_nonneg _)
    _ = (1 + ∑ j ∈ Finset.range N, |w (j + 1) - w j|) * (1 / (2 * |β|)) := by
        rw [← Finset.sum_mul]; ring
    _ ≤ (1 + 3) * (1 / (2 * |β|)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 2 / |β| := by field_simp [habs_pos.ne']; ring

end QuarticAndKernel

section OrthogonalityAndParseval

lemma continuous_e_mul (c : ℝ) : Continuous (fun α : ℝ => e (c * α)) := by
  unfold e
  have h : (fun α : ℝ => Complex.exp (2 * (Real.pi : ℂ) * ((c * α : ℝ) : ℂ) * Complex.I)) =
      fun α : ℝ => Complex.exp (((2 * Real.pi * c : ℝ) : ℂ) * Complex.I * (α : ℂ)) := by
    funext α; congr 1; push_cast; ring
  rw [h]
  exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)

/-- Exact orthogonality of `e (m * α)` on `[0, 1]` for `m : ℤ`. -/
theorem integral_e_int (m : ℤ) :
    (∫ α in (0 : ℝ)..1, e ((m : ℝ) * α)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [e_zero]
  · rw [ite_eq_right hm]
    let c : ℂ := 2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      have h1 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h2 : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h1) h2) Complex.I_ne_zero
    have hderiv : ∀ α ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c) (e ((m : ℝ) * α)) α := by
      intro α _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c α := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := α)).const_mul c
      have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (Complex.exp (c * (α : ℂ)) * c) α :=
        h1.cexp
      have h3 := h2.div_const c
      rw [mul_div_cancel_right₀ _ hc] at h3
      have heq : Complex.exp (c * (α : ℂ)) = e ((m : ℝ) * α) := by
        unfold e; congr 1; simp only [c]; push_cast; ring
      rwa [heq] at h3
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv ((continuous_e_mul (m : ℝ)).intervalIntegrable 0 1)]
    have h1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
      have : c * ((1 : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by simp [c]; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    have h0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [h1, h0, sub_self]

/-- Helper: finite sum of interval-integrable functions is interval-integrable. -/
lemma intervalIntegrable_finset_sum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (s : Finset ι) {f : ι → ℝ → E}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) MeasureTheory.volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | @insert i t hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Helper: interval integral of a finite sum of interval-integrable functions. -/
lemma intervalIntegral_finset_sum {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {s : Finset ι} {f : ι → ℝ → E}
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume a b) :
    (∫ x in a..b, ∑ i ∈ s, f i x) = ∑ i ∈ s, ∫ x in a..b, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    simp_rw [Finset.sum_insert hi]
    have h1 : IntervalIntegrable (f i) MeasureTheory.volume a b := hf i (Finset.mem_insert_self _ _)
    have h2 : IntervalIntegrable (fun x => ∑ j ∈ t, f j x) MeasureTheory.volume a b :=
      intervalIntegrable_finset_sum t fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [intervalIntegral.integral_add h1 h2, ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-- Exact orthogonality of `e (m * α)` on `[-1/2, 1/2]` for `m : ℤ`. -/
theorem integral_e_int_symm (m : ℤ) :
    (∫ α in (-(1 / 2) : ℝ)..(1 / 2), e ((m : ℝ) * α)) = if m = 0 then 1 else 0 := by
  have hper : Function.Periodic (fun α : ℝ => e ((m : ℝ) * α)) 1 := by
    intro α
    dsimp only
    have : (m : ℝ) * (α + 1) = (m : ℝ) * α + (m : ℤ) := by ring
    rw [this, e_add_int]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2) : ℝ) 0
  have hsimp1 : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  have hsimp2 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [hsimp1, hsimp2] at hshift
  rw [hshift, integral_e_int]

/-- Finite Parseval identity on `[0, 1]`. -/
theorem integral_norm_sq_trigPoly (M : ℕ) (f : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1, ‖∑ j ∈ Finset.range M, f j * e (α * (j : ℝ))‖ ^ 2) =
      ∑ j ∈ Finset.range M, ‖f j‖ ^ 2 := by
  have hpt : ∀ α : ℝ,
      ((‖∑ j ∈ Finset.range M, f j * e (α * (j : ℝ))‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M,
          f j * star (f k) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul']
    have hstar : star (e (α * (k : ℝ))) = e (-(α * (k : ℝ))) := by
      apply mul_left_cancel₀ (show e (α * (k : ℝ)) ≠ 0 from by unfold e; exact Complex.exp_ne_zero _)
      rw [e_mul_star_e, ← e_add, add_neg_cancel, e_zero]
    rw [hstar]
    have hexp : e (α * (j : ℝ)) * e (-(α * (k : ℝ))) =
        e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) := by
      rw [← e_add]; congr 1; push_cast; ring
    calc f j * e (α * (j : ℝ)) * (star (f k) * e (-(α * (k : ℝ))))
        = f j * star (f k) * (e (α * (j : ℝ)) * e (-(α * (k : ℝ)))) := by ring
      _ = f j * star (f k) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) := by rw [hexp]
  have hC : ((∫ α in (0 : ℝ)..1, ‖∑ j ∈ Finset.range M, f j * e (α * (j : ℝ))‖ ^ 2 : ℝ) : ℂ) =
      ((∑ j ∈ Finset.range M, ‖f j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    rw [intervalIntegral_finset_sum]
    · have hinner : ∀ j ∈ Finset.range M,
          (∫ α in (0 : ℝ)..1, ∑ k ∈ Finset.range M,
            f j * star (f k) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * α)) =
          ∑ k ∈ Finset.range M, ∫ α in (0 : ℝ)..1,
            f j * star (f k) * e ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * α) :=
        fun j _ => intervalIntegral_finset_sum fun k _ =>
          (continuous_const.mul (continuous_e_mul _)).intervalIntegrable 0 1
      rw [Finset.sum_congr rfl hinner]
      simp_rw [intervalIntegral.integral_const_mul, integral_e_int]
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.sum_eq_single j]
      · simp [Complex.mul_conj']
      · intro k _ hkj
        have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
        simp [hne]
      · intro hnj; exact absurd hj hnj
    · intro j _
      exact intervalIntegrable_finset_sum (Finset.range M) fun k _ =>
        (continuous_const.mul (continuous_e_mul ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ)))).intervalIntegrable 0 1
  exact_mod_cast hC

/-- Exact L² norm of `smoothedKernel` on `[-1/2, 1/2]` is at most `Y / r + 1`. -/
lemma smoothedKernel_l2_le (r b Y : ℕ) :
    (∫ β in (-(1 / 2) : ℝ)..(1 / 2), ‖smoothedKernel r b Y β‖ ^ 2) ≤ (Y : ℝ) / (r : ℝ) + 1 := by
  have hper : Function.Periodic (fun β : ℝ => ‖smoothedKernel r b Y β‖ ^ 2) 1 := by
    intro β
    dsimp only
    have hK : smoothedKernel r b Y (β + 1) = smoothedKernel r b Y β := by
      unfold smoothedKernel
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have : (β + 1) * (j : ℝ) = β * (j : ℝ) + (j : ℤ) := by push_cast; ring
      rw [this, e_add_int]
    rw [hK]
  have hshift := hper.intervalIntegral_add_eq (-(1 / 2) : ℝ) 0
  have h1 : -(1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  have h2 : (0 : ℝ) + 1 = 1 := by norm_num
  rw [h1, h2] at hshift
  rw [hshift]
  unfold smoothedKernel
  rw [integral_norm_sq_trigPoly]
  calc ∑ j ∈ Finset.range (Y / r + 1), ‖(quarticBump ((r * j + b : ℝ) / (Y : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ _j ∈ Finset.range (Y / r + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _)]
        nlinarith [quarticBump_nonneg ((r * j + b : ℝ) / (Y : ℝ)),
          quarticBump_le_one ((r * j + b : ℝ) / (Y : ℝ))]
    _ = ((Y / r + 1 : ℕ) : ℝ) := by simp
    _ ≤ (Y : ℝ) / (r : ℝ) + 1 := by
        by_cases hr : r = 0
        · subst hr; simp
        · have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
          have hdiv : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := by
            rw [le_div_iff₀ hr_pos]
            exact_mod_cast (by simpa [mul_comm] using Nat.mul_div_le Y r)
          push_cast; linarith

end OrthogonalityAndParseval

section PrincipalCharacterFormula

/-- Canonical representative of `r⁻¹ mod q` in `{0, ..., q - 1}`. -/
noncomputable def rInv (r q : ℕ) : ℕ := ((r : ZMod q)⁻¹).val

lemma mul_rInv_modEq {r q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime q r) :
    r * rInv r q ≡ 1 [MOD q] := by
  have : NeZero q := ⟨hq.ne'⟩
  have hu : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).2 hcop.symm
  have hc : ((r * rInv r q : ℕ) : ZMod q) = (1 : ZMod q) := by
    rw [Nat.cast_mul]
    change (r : ZMod q) * ((((r : ZMod q)⁻¹).val : ℕ) : ZMod q) = 1
    rw [ZMod.natCast_zmod_val, mul_comm]
    exact (ZMod.inv_mul_eq_one_of_isUnit hu (r : ZMod q)).2 rfl
  exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using hc)

lemma rInv_coprime {r q : ℕ} (hq : 0 < q) (hcop : Nat.Coprime q r) :
    Nat.Coprime (rInv r q) q := by
  have hmod := mul_rInv_modEq hq hcop
  apply Nat.coprime_of_dvd
  intro p hp hp1 hp2
  have h1 : p ∣ r * rInv r q := dvd_mul_of_dvd_right hp1 r
  have hmod_p : r * rInv r q ≡ 1 [MOD p] := hmod.of_dvd hp2
  have h0 : (r * rInv r q) % p = 0 := Nat.mod_eq_zero_of_dvd h1
  rw [Nat.ModEq, h0] at hmod_p
  exact hp.ne_one (Nat.dvd_one.mp (Nat.dvd_of_mod_eq_zero hmod_p.symm))

/-- Exact formula for the principal character coefficient when `Nat.Coprime q r`:
`e(-a*b/(rq)) * charCoeff r q a b 1 = e(-a * rInv r q * b / q) * μ(q) / (φ(r) * φ(q))`. -/
theorem charCoeff_one_coprime {r q a b : ℕ} (hr : 0 < r) (hq : 0 < q) (hb : b < r)
    (ha : Nat.Coprime a q) (hbr : Nat.Coprime b r) (hqr : Nat.Coprime q r) [NeZero (r * q)] :
    e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
        charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) =
      e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
        (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ)) := by
  classical
  have htot_mul : (r * q).totient = r.totient * q.totient := Nat.totient_mul hqr.symm
  -- Rewrite `charCoeff ... 1` as `(1 / φ(rq)) * ∑_{u ∈ charSupp r q b} e(a * u.val / (rq))`.
  have h1 : charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) =
      ((1 : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) := by
    unfold charCoeff charSupp
    rw [htot_mul, Nat.cast_mul]
    congr 1
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_unit := (Finset.mem_filter.mp hu).2.1
    rw [MulChar.one_apply hu_unit, star_one, mul_one]
  rw [h1]
  -- Biject `charSupp r q b` with `J = {j ∈ range q | Coprime (r * j + b) q}` via `j ↦ (r * j + b : ZMod (r*q))`.
  let J := (Finset.range q).filter (fun j => Nat.Coprime (r * j + b) q)
  have hsum_J : e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
      ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) =
      ∑ j ∈ J, e ((a : ℝ) * (j : ℝ) / (q : ℝ)) := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij (fun j _ => ((r * j + b : ℕ) : ZMod (r * q))) ?_ ?_ ?_ ?_
    · intro j hj
      have hj_lt : j < q := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hj_cop : Nat.Coprime (r * j + b) q := (Finset.mem_filter.mp hj).2
      have hlt_rq : r * j + b < r * q := by
        have h1 : r * j + r ≤ r * q := by
          have : r * (j + 1) ≤ r * q := Nat.mul_le_mul_left r (by omega)
          linarith
        omega
      have hcop_r : Nat.Coprime (r * j + b) r := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_mul_left_add_right, Nat.gcd_comm]
        exact hbr
      have hcop_rq : Nat.Coprime (r * j + b) (r * q) := hcop_r.mul_right hj_cop
      rw [charSupp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime _ _).2 hcop_rq, ?_⟩
      rw [ZMod.val_natCast_of_lt hlt_rq, Nat.mul_add_mod]
    · intro j₁ hj₁ j₂ hj₂ hEq
      have hlt1 : r * j₁ + b < r * q := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj₁).1
        have : r * (j₁ + 1) ≤ r * q := Nat.mul_le_mul_left r (by omega); nlinarith
      have hlt2 : r * j₂ + b < r * q := by
        have := Finset.mem_range.mp (Finset.mem_filter.mp hj₂).1
        have : r * (j₂ + 1) ≤ r * q := Nat.mul_le_mul_left r (by omega); nlinarith
      have hval := congrArg ZMod.val hEq
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hval
      exact Nat.eq_of_mul_eq_mul_left hr (by omega)
    · intro u hu
      have hu' := (Finset.mem_filter.mp hu).2
      have hu_lt : u.val < r * q := u.val_lt
      let j := u.val / r
      have hj_lt : j < q := Nat.div_lt_of_lt_mul hu_lt
      have huv : r * j + b = u.val := by
        have h1 := Nat.div_add_mod u.val r
        have hmod : u.val % r = b := by rw [hu'.2, Nat.mod_eq_of_lt hb]
        dsimp [j]; omega
      have hcop_rq : Nat.Coprime u.val (r * q) :=
        (ZMod.isUnit_iff_coprime u.val (r * q)).1 (by simpa using hu'.1)
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt,
        huv.symm ▸ hcop_rq.coprime_dvd_right (dvd_mul_left q r)⟩, ?_⟩
      rw [huv, ZMod.natCast_zmod_val]
    · intro j hj
      have hj_lt : j < q := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hlt_rq : r * j + b < r * q := by
        have : r * (j + 1) ≤ r * q := Nat.mul_le_mul_left r (by omega); nlinarith
      rw [ZMod.val_natCast_of_lt hlt_rq, ← e_add]
      congr 1
      have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      push_cast; field_simp [hr0, hq0]; ring
  -- Now evaluate `∑_{j ∈ J} e(a * j / q) = e(-a * rInv * b / q) * μ(q)`!
  have hsum_mu : ∑ j ∈ J, e ((a : ℝ) * (j : ℝ) / (q : ℝ)) =
      e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) * (ArithmeticFunction.moebius q : ℂ) := by
    rw [← ramanujanSum_right_one_eq_moebius hq, ramanujanSum, Finset.mul_sum]
    refine Finset.sum_bij (fun j _ => (a * rInv r q * (r * j + b)) % q) ?_ ?_ ?_ ?_
    · intro j hj
      have hj_cop : Nat.Coprime (r * j + b) q := (Finset.mem_filter.mp hj).2
      have hcop_all : Nat.Coprime (a * rInv r q * (r * j + b)) q :=
        (ha.mul_left (rInv_coprime hq hqr)).mul_left hj_cop
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ hq, ?_⟩
      rw [Nat.Coprime, Nat.ModEq.gcd_eq (Nat.mod_modEq _ q)]
      exact hcop_all.gcd_eq_one
    · intro j₁ hj₁ j₂ hj₂ hEq
      have hlt1 := Finset.mem_range.mp (Finset.mem_filter.mp hj₁).1
      have hlt2 := Finset.mem_range.mp (Finset.mem_filter.mp hj₂).1
      have hmod : a * rInv r q * (r * j₁ + b) ≡ a * rInv r q * (r * j₂ + b) [MOD q] := hEq
      have hcop_ar : Nat.Coprime (a * rInv r q) q := ha.mul_left (rInv_coprime hq hqr)
      have hmod2 : r * j₁ + b ≡ r * j₂ + b [MOD q] :=
        Nat.ModEq.cancel_left_of_coprime hcop_ar.symm hmod
      have hmod3 : r * j₁ ≡ r * j₂ [MOD q] := Nat.ModEq.add_right_cancel' b hmod2
      have hmod4 : j₁ ≡ j₂ [MOD q] := Nat.ModEq.cancel_left_of_coprime hqr hmod3
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hmod4
    · intro w hw
      have hw_lt := Finset.mem_range.mp (Finset.mem_filter.mp hw).1
      have hw_cop := (Finset.mem_filter.mp hw).2
      have : NeZero q := ⟨hq.ne'⟩
      let aInv : ℕ := ((a : ZMod q)⁻¹).val
      have ha_inv : a * aInv ≡ 1 [MOD q] := by
        have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).2 ha
        have hc : ((a * aInv : ℕ) : ZMod q) = 1 := by
          rw [Nat.cast_mul]; change (a : ZMod q) * ((((a : ZMod q)⁻¹).val : ℕ) : ZMod q) = 1
          rw [ZMod.natCast_zmod_val, mul_comm]; exact (ZMod.inv_mul_eq_one_of_isUnit hu _).2 rfl
        exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (by simpa using hc)
      -- Choose `j = ((aInv * w - rInv * b) mod q)`.
      let z : ZMod q := (aInv : ZMod q) * (w : ZMod q) - (rInv r q : ZMod q) * (b : ZMod q)
      let j : ℕ := z.val
      have hj_lt : j < q := z.val_lt
      have hrz : ((r * j + b : ℕ) : ZMod q) = (r : ZMod q) * (aInv : ZMod q) * (w : ZMod q) := by
        have hrr : (r : ZMod q) * (rInv r q : ZMod q) = 1 := by
          have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (mul_rInv_modEq hq hqr)
          simpa [Nat.cast_mul] using this
        push_cast
        change (r : ZMod q) * (z.val : ZMod q) + (b : ZMod q) = _
        rw [ZMod.natCast_zmod_val]
        simp only [z]
        calc (r : ZMod q) * ((aInv : ZMod q) * (w : ZMod q) - (rInv r q : ZMod q) * (b : ZMod q)) + (b : ZMod q)
            = (r : ZMod q) * (aInv : ZMod q) * (w : ZMod q) - ((r : ZMod q) * (rInv r q : ZMod q)) * (b : ZMod q) + (b : ZMod q) := by ring
          _ = (r : ZMod q) * (aInv : ZMod q) * (w : ZMod q) := by rw [hrr]; ring
      have htarget : ((a * rInv r q * (r * j + b) : ℕ) : ZMod q) = (w : ZMod q) := by
        have haa : (a : ZMod q) * (aInv : ZMod q) = 1 := by
          have := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha_inv
          simpa [Nat.cast_mul] using this
        have hrr : (r : ZMod q) * (rInv r q : ZMod q) = 1 := by
          have := (ZMod.natCast_eq_natCast_iff _ _ _).2 (mul_rInv_modEq hq hqr)
          simpa [Nat.cast_mul] using this
        rw [Nat.cast_mul, hrz]
        calc ((a * rInv r q : ℕ) : ZMod q) * ((r : ZMod q) * (aInv : ZMod q) * (w : ZMod q))
            = ((a : ZMod q) * (aInv : ZMod q)) * ((r : ZMod q) * (rInv r q : ZMod q)) * (w : ZMod q) := by
              push_cast; ring
          _ = (w : ZMod q) := by rw [haa, hrr]; ring
      have hcop_rj : Nat.Coprime (r * j + b) q := by
        rw [← ZMod.isUnit_iff_coprime, hrz]
        have hu_r : IsUnit (r : ZMod q) := (ZMod.isUnit_iff_coprime r q).2 hqr.symm
        have hu_w : IsUnit (w : ZMod q) := (ZMod.isUnit_iff_coprime w q).2 hw_cop
        have hu_aInv : IsUnit (aInv : ZMod q) := by
          have haa : (a : ZMod q) * (aInv : ZMod q) = 1 := by
            have := (ZMod.natCast_eq_natCast_iff _ _ _).2 ha_inv
            simpa [Nat.cast_mul] using this
          exact isUnit_iff_exists_inv'.2 ⟨(a : ZMod q), haa⟩
        exact (hu_r.mul hu_aInv).mul hu_w
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hcop_rj⟩, ?_⟩
      have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).1 htarget
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hw_lt] at hmod
    · intro j _
      rw [← e_add]
      -- Show `a * j / q` and `-a * rInv * b / q + ((a * rInv * (r * j + b)) % q) / q` differ by an integer!
      let rem := (a * rInv r q * (r * j + b)) % q
      have hmod1 : a * rInv r q * (r * j + b) ≡ rem [MOD q] := (Nat.mod_modEq _ q).symm
      have hmod2 : r * rInv r q ≡ 1 [MOD q] := mul_rInv_modEq hq hqr
      have hmod3 : a * j + a * rInv r q * b ≡ a * rInv r q * (r * j + b) [MOD q] := by
        have h1 : a * j * 1 ≡ a * j * (r * rInv r q) [MOD q] := hmod2.symm.mul_left (a * j)
        have h2 : a * j * 1 + a * rInv r q * b ≡ a * j * (r * rInv r q) + a * rInv r q * b [MOD q] :=
          h1.add_right _
        have heq1 : a * j * 1 + a * rInv r q * b = a * j + a * rInv r q * b := by ring
        have heq2 : a * j * (r * rInv r q) + a * rInv r q * b = a * rInv r q * (r * j + b) := by ring
        rwa [heq1, heq2] at h2
      have hmod_all : a * j + a * rInv r q * b ≡ rem [MOD q] := hmod3.trans hmod1
      have hdvd : (q : ℤ) ∣ ((a * j + a * rInv r q * b : ℕ) : ℤ) - (rem : ℤ) :=
        Int.ModEq.dvd (Int.natCast_modEq_iff.2 hmod_all).symm
      obtain ⟨k, hk⟩ := hdvd
      apply e_eq_of_sub_int (k := k)
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      have hkR : ((a * j + a * rInv r q * b : ℕ) : ℝ) - (rem : ℝ) = (q : ℝ) * (k : ℝ) := by
        exact_mod_cast hk
      have hnum : (a : ℝ) * (j : ℝ) - (-(a : ℝ) * (rInv r q : ℝ) * (b : ℝ) + (rem : ℝ)) =
          (q : ℝ) * (k : ℝ) := by
        have : ((a * j + a * rInv r q * b : ℕ) : ℝ) =
            (a : ℝ) * (j : ℝ) + (a : ℝ) * (rInv r q : ℝ) * (b : ℝ) := by push_cast; ring
        linarith
      simp only [Nat.cast_one, mul_one]
      field_simp [hq0]
      linarith
  calc e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
          (((1 : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)))
      = ((1 : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
          (e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ))) := by ring
    _ = ((1 : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ))) *
          (e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) * (ArithmeticFunction.moebius q : ℂ)) := by
        rw [hsum_J, hsum_mu]
    _ = e (-((a : ℝ) * (rInv r q : ℝ) * (b : ℝ) / (q : ℝ))) *
          (ArithmeticFunction.moebius q : ℂ) / ((r.totient : ℂ) * (q.totient : ℂ)) := by ring

end PrincipalCharacterFormula

section PrimeSumL2

/-- **Module B3b (Prime-sum L² bound from `SmoothedTwistEstimate`):**
Under `SmoothedTwistEstimate` with constant `C`, for `1 ≤ r ≤ Y`, `2 ≤ Y`, `b < r`, `Coprime b r`:
`∫ α in 0..1, ‖smoothedPrimeSum r b Y α‖² ≤ (r / φ(r) * (Y / r) + 2 * C * √Y * log(2Y)) * log(2Y)`. -/
theorem smoothedPrimeSum_l2_le {C : ℝ} (hC : 0 < C)
    (hTw : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (t : ℝ),
      2 ≤ Y → |t| ≤ 1 / 2 →
        ‖smoothedTiltedRemainder χ Y t‖ ≤
          C * Real.sqrt ((Y : ℝ) * (1 + |t| * Y)) * Real.log (2 * (d : ℝ) * Y))
    {r b Y : ℕ} (hr : 0 < r) (hrY : r ≤ Y) (hY : 2 ≤ Y) (hb : b < r) (hbr : Nat.Coprime b r) :
    (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) ≤
      (((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) +
        2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) * Real.log (2 * (Y : ℝ)) := by
  classical
  have : NeZero (r * 1) := ⟨by omega⟩
  have hL2 : (∫ α in (0 : ℝ)..1, ‖smoothedPrimeSum r b Y α‖ ^ 2) =
      ∑ j ∈ Finset.range (Y / r + 1),
        (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 := by
    unfold smoothedPrimeSum
    rw [integral_norm_sq_trigPoly]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hL2]
  -- Bound `w * primeWeight ≤ log(2Y)` on every term with `w > 0`.
  have hstep1 : ∑ j ∈ Finset.range (Y / r + 1),
        (quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b)) ^ 2 ≤
      (∑ j ∈ Finset.range (Y / r + 1),
        quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b)) *
        Real.log (2 * (Y : ℝ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    set x := (r * j + b : ℝ) / (Y : ℝ)
    by_cases hx : 0 < x ∧ x < 1
    · have hltY : r * j + b < Y := by
        have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
        have : (r * j + b : ℝ) < Y := (div_lt_one hYpos).1 hx.2
        exact_mod_cast (by simpa [Nat.cast_add, Nat.cast_mul] using this : ((r * j + b : ℕ) : ℝ) < (Y : ℝ))
      have hw_nn : 0 ≤ quarticBump x := quarticBump_nonneg x
      have hw_le : quarticBump x ≤ 1 := quarticBump_le_one x
      have hp_nn : 0 ≤ primeWeight (r * j + b) := primeWeight_nonneg _
      have hp_le_vm : primeWeight (r * j + b) ≤ ArithmeticFunction.vonMangoldt (r * j + b) :=
        primeWeight_le_vonMangoldt _
      have hp_le_log : primeWeight (r * j + b) ≤ Real.log (2 * (Y : ℝ)) :=
        (primeWeight_le_log hltY.le).trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < Y)) (by
          have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith))
      have hprod1 : quarticBump x * primeWeight (r * j + b) ≤ Real.log (2 * (Y : ℝ)) := by
        have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
          have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith)
        calc quarticBump x * primeWeight (r * j + b)
            ≤ 1 * Real.log (2 * (Y : ℝ)) := mul_le_mul hw_le hp_le_log hp_nn zero_le_one
          _ = Real.log (2 * (Y : ℝ)) := one_mul _
      have hprod2 : quarticBump x * primeWeight (r * j + b) ≤
          quarticBump x * ArithmeticFunction.vonMangoldt (r * j + b) :=
        mul_le_mul_of_nonneg_left hp_le_vm hw_nn
      rw [sq]
      exact mul_le_mul hprod2 hprod1 (mul_nonneg hw_nn hp_nn) (mul_nonneg hw_nn ArithmeticFunction.vonMangoldt_nonneg)
    · have hw0 : quarticBump x = 0 := by unfold quarticBump; simp [hx]
      simp [hw0]
  -- Reindex the `j`-sum into `n ∈ (Icc 1 Y).filter (fun n => n % r = b)` and expand via `charExpansion_eval` with `q = 1, a = 0`.
  have hsum_eq : ((∑ j ∈ Finset.range (Y / r + 1),
        quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ (r * 1),
        charCoeff r 1 0 b χ * smoothedTiltedRemainder χ Y 0 +
      charCoeff r 1 0 b 1 * ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
    have hreidx : ∑ j ∈ Finset.range (Y / r + 1),
        quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) =
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
          quarticBump ((n : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n := by
      let J0 := (Finset.range (Y / r + 1)).filter (fun j => 1 ≤ r * j + b ∧ r * j + b ≤ Y)
      have htrim : ∑ j ∈ Finset.range (Y / r + 1),
          quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) =
          ∑ j ∈ J0, quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) := by
        symm
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h
        · rfl
        · have hw0 : quarticBump ((r * j + b : ℝ) / (Y : ℝ)) = 0 := by
            unfold quarticBump
            have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
            have hnot : ¬ (0 < (r * j + b : ℝ) / (Y : ℝ) ∧ (r * j + b : ℝ) / (Y : ℝ) < 1) := by
              rintro ⟨h1, h2⟩
              have h1' : (0 : ℝ) < (r * j + b : ℝ) := (div_pos_iff_of_pos_right hYpos).1 h1
              have h2' : (r * j + b : ℝ) < (Y : ℝ) := (div_lt_one hYpos).1 h2
              have hcast : ((r * j + b : ℕ) : ℝ) = (r * j + b : ℝ) := by push_cast; rfl
              have hn1 : 1 ≤ r * j + b := by
                rw [← hcast] at h1'
                have : (0 : ℕ) < r * j + b := by exact_mod_cast h1'
                omega
              have hn2 : r * j + b ≤ Y := by
                rw [← hcast] at h2'
                have : r * j + b < Y := by exact_mod_cast h2'
                omega
              exact h ⟨hn1, hn2⟩
            simp [hnot]
          simp [hw0]
      rw [htrim]
      refine Finset.sum_bij (fun j _ => r * j + b) ?_ ?_ ?_ ?_
      · intro j hj
        have hmem := (Finset.mem_filter.mp hj).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hmem, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      · intro j₁ _ j₂ _ hEq
        exact Nat.eq_of_mul_eq_mul_left hr (by omega)
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hmod := (Finset.mem_filter.mp hn).2
        let j := n / r
        have hnj : r * j + b = n := by
          have := Nat.div_add_mod n r; dsimp [j]; omega
        have hj_lt : j < Y / r + 1 := Nat.lt_succ_of_le (Nat.div_le_div_right hIcc.2)
        refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj_lt, hnj.symm ▸ hIcc.1, hnj.symm ▸ hIcc.2⟩, hnj⟩
      · intro j _; push_cast; rfl
    rw [hreidx, Complex.ofReal_sum]
    have hexpand : ∀ n ∈ Finset.Icc 1 Y,
        (if n % r = b then ((quarticBump ((n : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0) =
        ∑ χ : DirichletCharacter ℂ (r * 1),
          charCoeff r 1 0 b χ *
            (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * 1))) *
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
      intro n _
      by_cases hu : IsUnit (n : ZMod (r * 1))
      · have heval := charExpansion_eval r 1 0 b hr one_pos hu
        have hval_mod : ((n : ZMod (r * 1)).val) % r = n % r := by
          rw [ZMod.val_natCast, mul_one, Nat.mod_mod]
        have hb_mod : b % r = b := Nat.mod_eq_of_lt hb
        rw [hval_mod, hb_mod] at heval
        have he0 : e (((0 : ℕ) : ℝ) * ((n : ZMod (r * 1)).val : ℝ) / ((r * 1 : ℕ) : ℝ)) = 1 := by
          simp [e_zero]
        rw [he0] at heval
        calc (if n % r = b then ((quarticBump ((n : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
            = (if n % r = b then (1 : ℂ) else 0) *
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
              split_ifs <;> simp [mul_comm]
          _ = (∑ χ : DirichletCharacter ℂ (r * 1), charCoeff r 1 0 b χ * χ (n : ZMod (r * 1))) *
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
              rw [heval]
          _ = ∑ χ : DirichletCharacter ℂ (r * 1),
                charCoeff r 1 0 b χ * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * 1))) *
                  (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
              rw [Finset.sum_mul, Finset.sum_mul]
              refine Finset.sum_congr rfl fun χ _ => by ring
      · have hnotb : n % r ≠ b := by
          intro hmod
          have hcop : Nat.Coprime n (r * 1) := by
            rw [mul_one, Nat.Coprime, Nat.ModEq.gcd_eq (show n ≡ b [MOD r] by rw [Nat.ModEq, hmod, Nat.mod_eq_of_lt hb])]
            exact hbr.gcd_eq_one
          exact hu ((ZMod.isUnit_iff_coprime n (r * 1)).2 hcop)
        rw [ite_eq_right hnotb]
        symm
        apply Finset.sum_eq_zero
        intro χ _
        rw [MulChar.map_nonunit χ hu]
        ring
    rw [Finset.sum_filter]
    calc ∑ n ∈ Finset.Icc 1 Y,
          (if n % r = b then ((quarticBump ((n : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) else 0)
        = ∑ n ∈ Finset.Icc 1 Y, ∑ χ : DirichletCharacter ℂ (r * 1),
            charCoeff r 1 0 b χ * (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * 1))) *
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) :=
          Finset.sum_congr rfl hexpand
      _ = ∑ χ : DirichletCharacter ℂ (r * 1), charCoeff r 1 0 b χ *
            ∑ n ∈ Finset.Icc 1 Y,
              (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod (r * 1))) *
                (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => by ring
      _ = ∑ χ : DirichletCharacter ℂ (r * 1),
            charCoeff r 1 0 b χ *
              (smoothedTiltedRemainder χ Y 0 +
                (if χ = 1 then (1 : ℂ) else 0) * ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          congr 1
          unfold smoothedTiltedRemainder
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          simp only [zero_mul, e_zero, mul_one]
          ring
      _ = ∑ χ : DirichletCharacter ℂ (r * 1), charCoeff r 1 0 b χ * smoothedTiltedRemainder χ Y 0 +
            charCoeff r 1 0 b 1 * ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
          congr 1
          rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ (r * 1))]
          · simp
          · intro χ _ hχ; simp [hχ]
          · intro h; exact absurd (Finset.mem_univ _) h
  -- Take norms on `hsum_eq`!
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (Y / r + 1),
      quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (quarticBump_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  have hsum_le : ∑ j ∈ Finset.range (Y / r + 1),
        quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) ≤
      ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) +
        2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) := by
    have hnorm : ∑ j ∈ Finset.range (Y / r + 1),
        quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) =
        ‖((∑ j ∈ Finset.range (Y / r + 1),
          quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * ArithmeticFunction.vonMangoldt (r * j + b) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum_nn]
    rw [hnorm, hsum_eq]
    have h1 : ‖∑ χ : DirichletCharacter ℂ (r * 1), charCoeff r 1 0 b χ * smoothedTiltedRemainder χ Y 0‖ ≤
        2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) := by
      have hl1 := charCoeff_l1_le r 1 0 b hr one_pos hbr
      have hgcd1 : Real.sqrt (((1 : ℕ) : ℝ) / ((Nat.gcd r 1 : ℕ) : ℝ)) = 1 := by simp
      rw [hgcd1] at hl1
      have hlog : Real.log (2 * (r : ℝ) * (Y : ℝ)) ≤ 2 * Real.log (2 * (Y : ℝ)) := by
        have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
        have h2Y : 2 * (r : ℝ) * (Y : ℝ) ≤ (2 * (Y : ℝ)) ^ 2 := by
          have hrY' : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
          nlinarith
        calc Real.log (2 * (r : ℝ) * (Y : ℝ))
            ≤ Real.log ((2 * (Y : ℝ)) ^ 2) := Real.log_le_log (by positivity) h2Y
          _ = 2 * Real.log (2 * (Y : ℝ)) := by rw [Real.log_pow]; norm_num
      calc ‖∑ χ : DirichletCharacter ℂ (r * 1), charCoeff r 1 0 b χ * smoothedTiltedRemainder χ Y 0‖
          ≤ ∑ χ : DirichletCharacter ℂ (r * 1), ‖charCoeff r 1 0 b χ‖ * ‖smoothedTiltedRemainder χ Y 0‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => (norm_mul _ _).le)
        _ ≤ ∑ χ : DirichletCharacter ℂ (r * 1),
              ‖charCoeff r 1 0 b χ‖ * (2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) := by
            refine Finset.sum_le_sum fun χ _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            have htw := hTw Y (r * 1) χ 0 hY (by norm_num)
            simp only [abs_zero, zero_mul, add_zero, mul_one] at htw
            calc ‖smoothedTiltedRemainder χ Y 0‖
                ≤ C * Real.sqrt (Y : ℝ) * Real.log (2 * (r : ℝ) * (Y : ℝ)) := htw
              _ ≤ C * Real.sqrt (Y : ℝ) * (2 * Real.log (2 * (Y : ℝ))) :=
                  mul_le_mul_of_nonneg_left hlog (by positivity)
              _ = 2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) := by ring
        _ = (∑ χ : DirichletCharacter ℂ (r * 1), ‖charCoeff r 1 0 b χ‖) *
              (2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * (2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ))) := by
            have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
              have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith)
            exact mul_le_mul_of_nonneg_right hl1 (by positivity)
        _ = 2 * C * Real.sqrt (Y : ℝ) * Real.log (2 * (Y : ℝ)) := one_mul _
    have h2 : ‖charCoeff r 1 0 b 1 * ∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)‖ ≤
        ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) := by
      have hcc := charCoeff_one_coprime hr one_pos hb (Nat.coprime_one_right 0) hbr (Nat.coprime_one_left r)
      simp only [Nat.cast_zero, zero_mul, zero_div, neg_zero, e_zero, one_mul,
        ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.totient_one, Nat.cast_one, mul_one] at hcc
      rw [norm_mul, hcc, norm_div, norm_one, Complex.norm_natCast]
      have hsum_w : ‖∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)‖ ≤ (Y : ℝ) := by
        calc ‖∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)‖
            ≤ ∑ n ∈ Finset.Icc 1 Y, ‖(quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.Icc 1 Y, (1 : ℝ) := by
              refine Finset.sum_le_sum fun n _ => ?_
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (quarticBump_nonneg _)]
              exact quarticBump_le_one _
          _ = (Y : ℝ) := by simp
      have htot_pos : (0 : ℝ) < r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
      have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
      calc (1 / (r.totient : ℝ)) * ‖∑ n ∈ Finset.Icc 1 Y, (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ)‖
          ≤ (1 / (r.totient : ℝ)) * (Y : ℝ) := mul_le_mul_of_nonneg_left hsum_w (by positivity)
        _ = ((r : ℝ) / (r.totient : ℝ)) * ((Y : ℝ) / (r : ℝ)) := by field_simp [hr0, htot_pos.ne']
    exact (norm_add_le _ _).trans (by linarith)
  have hlog_nn : 0 ≤ Real.log (2 * (Y : ℝ)) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ Y := Nat.cast_le.mpr hY; linarith)
  exact hstep1.trans (mul_le_mul_of_nonneg_right hsum_le hlog_nn)

end PrimeSumL2

end FareyGoldbach
