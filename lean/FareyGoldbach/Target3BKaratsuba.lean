import FareyGoldbach.Defs

open scoped BigOperators

namespace Target3B

private theorem finsupp_sum_apply {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → ℕ →₀ ℕ) (p : ℕ) :
    (∑ i ∈ s, g i) p = ∑ i ∈ s, g i p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finsupp.add_apply, ih]

private theorem nat_le_of_sq_le_sq {a b : ℕ} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  have hba : b < a := Nat.lt_of_not_ge hlt
  have hsq : b * b < a * a := Nat.mul_lt_mul'' hba hba
  rw [← sq, ← sq] at hsq
  omega

private theorem finset_lcm_ne_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) : s.lcm f ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    rw [Finset.lcm_insert]
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a t)
    have ht0 : t.lcm f ≠ 0 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact Nat.lcm_ne_zero ha0 ht0

/-- Karatsuba–Bourgain–Garaev LCM lemma: if positive integers `f i` satisfy a signed
unit-fraction identity `∑ σ i / f i = 0` with `σ i ∈ {1, -1}`, then the square of
`lcm (f i)` divides `∏ f i`. Every prime attains its maximum valuation in at least two
denominators, otherwise clearing denominators leaves a single nonzero term modulo `p`. -/
theorem karatsuba_lcm_sq_dvd_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (σ : ι → ℤ)
    (hf : ∀ i ∈ s, 0 < f i)
    (hσ : ∀ i ∈ s, σ i = 1 ∨ σ i = -1)
    (hsum : ∑ i ∈ s, (σ i : ℚ) / (f i : ℚ) = 0) :
    (s.lcm f) ^ 2 ∣ ∏ i ∈ s, f i := by
  let M := s.lcm f
  have hf_ne : ∀ i ∈ s, f i ≠ 0 := fun i hi => (hf i hi).ne'
  have hM_ne : M ≠ 0 := finset_lcm_ne_zero s f hf_ne
  have hM_pos : 0 < M := Nat.pos_of_ne_zero hM_ne
  have hP_ne : (∏ i ∈ s, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hf_ne
  have hM_dvd : ∀ i ∈ s, f i ∣ M := fun i hi => Finset.dvd_lcm hi
  have hZ : ∑ i ∈ s, σ i * ((M / f i : ℕ) : ℤ) = 0 := by
    have hQ : ((∑ i ∈ s, σ i * ((M / f i : ℕ) : ℤ) : ℤ) : ℚ) = 0 := by
      rw [Int.cast_sum]
      have hterm : ∀ i ∈ s,
          ((σ i * ((M / f i : ℕ) : ℤ) : ℤ) : ℚ) = (M : ℚ) * ((σ i : ℚ) / (f i : ℚ)) := by
        intro i hi
        rw [Int.cast_mul, Int.cast_natCast]
        have hfi_q : (f i : ℚ) ≠ 0 := by exact_mod_cast hf_ne i hi
        have hmul : ((M / f i : ℕ) : ℚ) * (f i : ℚ) = (M : ℚ) := by
          exact_mod_cast Nat.div_mul_cancel (hM_dvd i hi)
        field_simp [hfi_q]
        rw [mul_assoc, hmul]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum, mul_zero]
    exact Int.cast_eq_zero.mp hQ
  rw [← Nat.factorization_le_iff_dvd (pow_ne_zero 2 hM_ne) hP_ne]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_prod hf_ne, finsupp_sum_apply]
  set v := M.factorization p
  by_cases hv : v = 0
  · rw [hv, mul_zero]
    exact Nat.zero_le _
  have hv_pos : 0 < v := Nat.pos_of_ne_zero hv
  have hp : p.Prime := by
    by_contra hnp
    exact hv (Nat.factorization_eq_zero_of_not_prime M hnp)
  have hp_dvd_M : p ∣ M := (hp.dvd_iff_one_le_factorization hM_ne).mpr hv_pos
  have hle_v : ∀ i ∈ s, (f i).factorization p ≤ v := by
    intro i hi
    exact (Nat.factorization_le_iff_dvd (hf_ne i hi) hM_ne).mpr (hM_dvd i hi) p
  -- At least one denominator attains the maximum `p`-adic valuation `v`.
  have hex₁ : ∃ i₀ ∈ s, (f i₀).factorization p = v := by
    by_contra hnone
    push Not at hnone
    have hlt : ∀ i ∈ s, (f i).factorization p < v :=
      fun i hi => lt_of_le_of_ne (hle_v i hi) (hnone i hi)
    have hMp_ne : M / p ≠ 0 := by
      have hp_le : p ≤ M := Nat.le_of_dvd hM_pos hp_dvd_M
      exact (Nat.div_pos hp_le hp.pos).ne'
    have hdvd_Mp : ∀ i ∈ s, f i ∣ M / p := by
      intro i hi
      rw [← Nat.factorization_le_iff_dvd (hf_ne i hi) hMp_ne]
      intro q
      rw [Nat.factorization_div hp_dvd_M, Finsupp.tsub_apply]
      by_cases hqp : q = p
      · subst hqp
        rw [hp.factorization_self]
        have := hlt i hi
        omega
      · rw [hp.factorization, Finsupp.single_eq_of_ne hqp, Nat.sub_zero]
        exact (Nat.factorization_le_iff_dvd (hf_ne i hi) hM_ne).mpr (hM_dvd i hi) q
    have hM_dvd_Mp : M ∣ M / p := Finset.lcm_dvd hdvd_Mp
    have hle_div : M ≤ M / p := Nat.le_of_dvd (Nat.pos_of_ne_zero hMp_ne) hM_dvd_Mp
    have hdiv_lt : M / p < M := Nat.div_lt_self hM_pos hp.one_lt
    omega
  obtain ⟨i₀, hi₀, hfi₀⟩ := hex₁
  -- A second distinct denominator must also attain valuation `v`.
  have hex₂ : ∃ j₀ ∈ s, j₀ ≠ i₀ ∧ (f j₀).factorization p = v := by
    by_contra huniq
    push Not at huniq
    have hdvd_other : ∀ j ∈ s.erase i₀, (p : ℤ) ∣ σ j * ((M / f j : ℕ) : ℤ) := by
      intro j hj
      have hj_mem : j ∈ s := Finset.mem_of_mem_erase hj
      have hj_ne : j ≠ i₀ := Finset.ne_of_mem_erase hj
      have hj_lt : (f j).factorization p < v :=
        lt_of_le_of_ne (hle_v j hj_mem) (huniq j hj_mem hj_ne)
      have hdiv_ne : M / f j ≠ 0 := by
        have hle : f j ≤ M := Nat.le_of_dvd hM_pos (hM_dvd j hj_mem)
        exact (Nat.div_pos hle (hf j hj_mem)).ne'
      have hp_dvd_quot : p ∣ M / f j := by
        rw [hp.dvd_iff_one_le_factorization hdiv_ne,
          Nat.factorization_div (hM_dvd j hj_mem), Finsupp.tsub_apply]
        omega
      exact dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hp_dvd_quot) (σ j)
    have hdvd_sum : (p : ℤ) ∣ ∑ j ∈ s.erase i₀, σ j * ((M / f j : ℕ) : ℤ) :=
      Finset.dvd_sum hdvd_other
    have hsplit : σ i₀ * ((M / f i₀ : ℕ) : ℤ) +
        ∑ j ∈ s.erase i₀, σ j * ((M / f j : ℕ) : ℤ) = 0 := by
      rw [Finset.add_sum_erase s (fun j => σ j * ((M / f j : ℕ) : ℤ)) hi₀, hZ]
    have hdvd_i₀ : (p : ℤ) ∣ σ i₀ * ((M / f i₀ : ℕ) : ℤ) := by
      have : σ i₀ * ((M / f i₀ : ℕ) : ℤ) = -(∑ j ∈ s.erase i₀, σ j * ((M / f j : ℕ) : ℤ)) := by
        linarith
      rw [this]
      exact dvd_neg.mpr hdvd_sum
    have hdvd_quot_z : (p : ℤ) ∣ ((M / f i₀ : ℕ) : ℤ) := by
      rcases hσ i₀ hi₀ with h1 | hm1
      · simpa [h1] using hdvd_i₀
      · rw [hm1, neg_one_mul] at hdvd_i₀
        exact dvd_neg.mp hdvd_i₀
    have hp_dvd_quot : p ∣ M / f i₀ := Int.natCast_dvd_natCast.mp hdvd_quot_z
    have hdiv_ne : M / f i₀ ≠ 0 := by
      have hle : f i₀ ≤ M := Nat.le_of_dvd hM_pos (hM_dvd i₀ hi₀)
      exact (Nat.div_pos hle (hf i₀ hi₀)).ne'
    have h1le : 1 ≤ (M / f i₀).factorization p :=
      (hp.dvd_iff_one_le_factorization hdiv_ne).mp hp_dvd_quot
    rw [Nat.factorization_div (hM_dvd i₀ hi₀), Finsupp.tsub_apply, hfi₀] at h1le
    omega
  obtain ⟨j₀, hj₀, hne, hfj₀⟩ := hex₂
  have hsub : ({i₀, j₀} : Finset ι) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  calc
    2 * v = (f i₀).factorization p + (f j₀).factorization p := by rw [hfi₀, hfj₀]; ring
    _ = ∑ i ∈ ({i₀, j₀} : Finset ι), (f i).factorization p := by
      rw [Finset.sum_pair hne.symm]
    _ ≤ ∑ i ∈ s, (f i).factorization p := Finset.sum_le_sum_of_subset hsub

theorem karatsuba_lcm_sq_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (σ : ι → ℤ)
    (hf : ∀ i ∈ s, 0 < f i)
    (hσ : ∀ i ∈ s, σ i = 1 ∨ σ i = -1)
    (hsum : ∑ i ∈ s, (σ i : ℚ) / (f i : ℚ) = 0) :
    (s.lcm f) ^ 2 ≤ ∏ i ∈ s, f i :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i hi => (hf i hi).ne'))
    (karatsuba_lcm_sq_dvd_prod s f σ hf hσ hsum)

/-- Fourth-moment (`k = 2`) specialization: `1/a₁ + 1/a₂ = 1/b₁ + 1/b₂` implies
`lcm(a₁, a₂, b₁, b₂)^2 ∣ a₁ a₂ b₁ b₂`, so `M ≤ 4 W²` when all denominators are `≤ 2 W`. -/
theorem karatsuba_four_reciprocals {a₁ a₂ b₁ b₂ W : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (hW₁ : a₁ ≤ 2 * W) (hW₂ : a₂ ≤ 2 * W) (hW₃ : b₁ ≤ 2 * W) (hW₄ : b₂ ≤ 2 * W)
    (heq : (1 : ℚ) / a₁ + 1 / a₂ = 1 / b₁ + 1 / b₂) :
    let M := (Finset.univ : Finset (Fin 4)).lcm ![a₁, a₂, b₁, b₂]
    M ^ 2 ∣ a₁ * a₂ * b₁ * b₂ ∧ M ≤ 4 * W ^ 2 := by
  let f : Fin 4 → ℕ := ![a₁, a₂, b₁, b₂]
  let σ : Fin 4 → ℤ := ![1, 1, -1, -1]
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 < f i := by
    intro i _; fin_cases i <;> assumption
  have hσ : ∀ i ∈ (Finset.univ : Finset (Fin 4)), σ i = 1 ∨ σ i = -1 := by
    intro i _; fin_cases i <;> simp [σ]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 4)), (σ i : ℚ) / (f i : ℚ) = 0 := by
    rw [Fin.sum_univ_four]
    simp only [f, σ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast
    linear_combination heq
  have hdvd := karatsuba_lcm_sq_dvd_prod Finset.univ f σ hf hσ hsum
  have hprod : (∏ i ∈ (Finset.univ : Finset (Fin 4)), f i) = a₁ * a₂ * b₁ * b₂ := by
    rw [Fin.prod_univ_four]
    simp [f, mul_assoc]
  rw [hprod] at hdvd
  refine ⟨hdvd, ?_⟩
  have hsq : ((Finset.univ : Finset (Fin 4)).lcm f) ^ 2 ≤ (4 * W ^ 2) ^ 2 := by
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hbound : a₁ * a₂ * b₁ * b₂ ≤ (2 * W) * (2 * W) * (2 * W) * (2 * W) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hW₁ hW₂) hW₃) hW₄
    calc
      ((Finset.univ : Finset (Fin 4)).lcm f) ^ 2 ≤ a₁ * a₂ * b₁ * b₂ := hle
      _ ≤ (2 * W) * (2 * W) * (2 * W) * (2 * W) := hbound
      _ = (4 * W ^ 2) ^ 2 := by ring
  exact nat_le_of_sq_le_sq hsq

/-- Sixth-moment (`k = 3`) specialization: `1/a₁ + 1/a₂ + 1/a₃ = 1/b₁ + 1/b₂ + 1/b₃` implies
`lcm(a₁, a₂, a₃, b₁, b₂, b₃)^2 ∣ a₁ a₂ a₃ b₁ b₂ b₃` and `M ≤ 8 L³` when all denominators
are `≤ 2 L`. This powers the elementary `8/17` and spectral `7/15` thresholds. -/
theorem karatsuba_six_reciprocals {a₁ a₂ a₃ b₁ b₂ b₃ L : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 0 < b₃)
    (hL₁ : a₁ ≤ 2 * L) (hL₂ : a₂ ≤ 2 * L) (hL₃ : a₃ ≤ 2 * L)
    (hL₄ : b₁ ≤ 2 * L) (hL₅ : b₂ ≤ 2 * L) (hL₆ : b₃ ≤ 2 * L)
    (heq : (1 : ℚ) / a₁ + 1 / a₂ + 1 / a₃ = 1 / b₁ + 1 / b₂ + 1 / b₃) :
    let M := (Finset.univ : Finset (Fin 6)).lcm ![a₁, a₂, a₃, b₁, b₂, b₃]
    M ^ 2 ∣ a₁ * a₂ * a₃ * b₁ * b₂ * b₃ ∧ M ≤ 8 * L ^ 3 := by
  let f : Fin 6 → ℕ := ![a₁, a₂, a₃, b₁, b₂, b₃]
  let σ : Fin 6 → ℤ := ![1, 1, 1, -1, -1, -1]
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 0 < f i := by
    intro i _; fin_cases i <;> assumption
  have hσ : ∀ i ∈ (Finset.univ : Finset (Fin 6)), σ i = 1 ∨ σ i = -1 := by
    intro i _; fin_cases i <;> simp [σ]
  have hsum : ∑ i ∈ (Finset.univ : Finset (Fin 6)), (σ i : ℚ) / (f i : ℚ) = 0 := by
    rw [Fin.sum_univ_six]
    simp only [f, σ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    push_cast
    linear_combination heq
  have hdvd := karatsuba_lcm_sq_dvd_prod Finset.univ f σ hf hσ hsum
  have hprod : (∏ i ∈ (Finset.univ : Finset (Fin 6)), f i) = a₁ * a₂ * a₃ * b₁ * b₂ * b₃ := by
    rw [Fin.prod_univ_six]
    simp [f, mul_assoc]
  rw [hprod] at hdvd
  refine ⟨hdvd, ?_⟩
  have hsq : ((Finset.univ : Finset (Fin 6)).lcm f) ^ 2 ≤ (8 * L ^ 3) ^ 2 := by
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hbound :
        a₁ * a₂ * a₃ * b₁ * b₂ * b₃ ≤
          (2 * L) * (2 * L) * (2 * L) * (2 * L) * (2 * L) * (2 * L) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul hL₁ hL₂) hL₃) hL₄) hL₅) hL₆
    calc
      ((Finset.univ : Finset (Fin 6)).lcm f) ^ 2 ≤ a₁ * a₂ * a₃ * b₁ * b₂ * b₃ := hle
      _ ≤ (2 * L) * (2 * L) * (2 * L) * (2 * L) * (2 * L) * (2 * L) := hbound
      _ = (8 * L ^ 3) ^ 2 := by ring
  exact nat_le_of_sq_le_sq hsq

end Target3B
