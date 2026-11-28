import FareyGoldbach.ChenSwitching

/-! # The elementary loss and the floored Chen inequality -/

namespace FareyGoldbach

open scoped Classical

/-- Cover the exceptional complements by units, reflected prime divisors of `N`,
reflected small primes, and positive multiples of a square. -/
theorem chenBadSet_card_le_sum {N z y : ℕ} (hN : 0<N) :
    (chenBadSet N z y).card ≤ 2+N.primeFactors.card+y+
      ∑ d ∈ Finset.Ico z (N+1), N/d^2 := by
  classical
  let D := N.primeFactors.image (fun p ↦ N-p)
  let P := (Finset.range y).image (fun p ↦ N-p)
  let square (d : ℕ) := (Finset.Ioc 0 N).filter (d^2 ∣ ·)
  let S := (Finset.Ico z (N+1)).biUnion square
  have hD : D.card≤N.primeFactors.card := Finset.card_image_le
  have hP : P.card≤y := Finset.card_image_le.trans (by simp)
  have hS : S.card ≤ ∑ d ∈ Finset.Ico z (N+1), N/d^2 := by
    exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun d _ ↦ (Nat.Ioc_filter_dvd_card_eq_div N (d^2)).le)
  have hsub : chenBadSet N z y ⊆ ((Finset.range 2 ∪ D) ∪ P) ∪ S := by
    intro a ha
    obtain ⟨hsift,hbad⟩ := Finset.mem_filter.mp ha
    obtain ⟨haA,hrough⟩ := Finset.mem_filter.mp hsift
    obtain ⟨hbound,hp⟩ := Finset.mem_filter.mp haA
    have haN : a≤N := by simpa using Finset.mem_range.mp hbound
    simp only [Finset.mem_union,Finset.mem_range]
    by_cases hsmall : a<2
    · exact Or.inl (Or.inl (Or.inl hsmall))
    by_cases hcop : a.Coprime N
    · rcases hbad with hf | hf | hf | hf
      · contradiction
      · contradiction
      · rw [Nat.squarefree_iff_prime_squarefree] at hf
        push Not at hf
        obtain ⟨q,hqp,hdiv⟩ := hf
        have hqa : q∣a := dvd_trans (dvd_mul_right q q) hdiv
        have hq := Nat.mem_primeFactors.mpr ⟨hqp,hqa,by omega⟩
        have hqz := chenRough_primeFactors hrough hcop q hq
        have hqN := (Nat.le_of_dvd (by omega : 0<a) hqa).trans haN
        exact Or.inr (Finset.mem_biUnion.mpr ⟨q,Finset.mem_Ico.mpr ⟨hqz,by omega⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega,haN⟩,by simpa only [sq] using hdiv⟩⟩)
      · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨N-a,Finset.mem_range.mpr hf,by omega⟩))
    · obtain ⟨q,hqp,hqa,hqN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
      have hqd := Nat.dvd_sub hqN hqa
      have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hqd
      exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr
        ⟨q,Nat.mem_primeFactors.mpr ⟨hqp,hqN,hN.ne'⟩,by omega⟩)))
  have hu₁ := Finset.card_union_le (Finset.range 2) D
  have hu₂ := Finset.card_union_le (Finset.range 2∪D) P
  have hu₃ := Finset.card_union_le ((Finset.range 2∪D)∪P) S
  have hh := Finset.card_le_card hsub
  simp only [Finset.card_range] at hu₁
  omega

private theorem reciprocal_square_tail (z T : ℕ) (hz : 2≤z) :
    (∑ d ∈ Finset.Ico z T, 1/(d:ℝ)^2) ≤ 1/((z:ℝ)-1) := by
  by_cases hzT : z≤T
  · have htel : (∑ d ∈ Finset.Ico z T, 1/(d:ℝ)^2) ≤ 1/((z:ℝ)-1)-1/((T:ℝ)-1) := by
      induction T,hzT using Nat.le_induction with
      | base => simp
      | succ d hd ih =>
        have hd₂ : (2:ℝ)≤d := by exact_mod_cast hz.trans hd
        have h₀ : (0:ℝ)<d := by linarith
        have h₁ : 0<(d:ℝ)-1 := by linarith
        have hs : 1/(d:ℝ)^2 ≤ 1/((d:ℝ)-1)-1/(d:ℝ) := by
          field_simp
          nlinarith
        rw [Finset.sum_Ico_succ_top hd,Nat.cast_succ,add_sub_cancel_right]
        linarith only [ih,hs]
    have hT : (2:ℝ)≤T := by exact_mod_cast hz.trans hzT
    linarith only [htel,one_div_nonneg.mpr (by linarith : 0≤(T:ℝ)-1)]
  · rw [Finset.Ico_eq_empty_of_le (by omega),Finset.sum_empty]
    exact one_div_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast (show 1≤z by omega)))

theorem chen_square_quotient_sum_bound (N z : ℕ) (hz : 2≤z) :
    (∑ d ∈ Finset.Ico z (N+1), ((N/d^2:ℕ):ℝ)) ≤ (N:ℝ)/((z:ℝ)-1) := by
  have hterm (d : ℕ) : ((N/d^2:ℕ):ℝ) ≤ (N:ℝ)*(1/(d:ℝ)^2) := by
    have hd : ((N/d^2:ℕ):ℝ) ≤ (N:ℝ)/((d^2:ℕ):ℝ) := Nat.cast_div_le
    rw [Nat.cast_pow] at hd
    rw [mul_one_div]
    exact hd
  have hsum := Finset.sum_le_sum (s:=Finset.Ico z (N+1)) (fun d _ ↦ hterm d)
  rw [← Finset.mul_sum] at hsum
  have htail := mul_le_mul_of_nonneg_left (reciprocal_square_tail z (N+1) hz) (Nat.cast_nonneg (α:=ℝ) N)
  simpa only [mul_one_div] using hsum.trans htail

/-- A finite bound uniform in both integer cutoffs. -/
theorem chenBadSet_card_bound {N z y : ℕ} (hN : 0<N) (hz : 2≤z) :
    ((chenBadSet N z y).card:ℝ) ≤ 2+(N.primeFactors.card:ℝ)+y+(N:ℝ)/((z:ℝ)-1) := by
  have hc := (Nat.cast_le (α:=ℝ)).mpr (chenBadSet_card_le_sum (z:=z) (y:=y) hN)
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_sum] at hc
  exact hc.trans (add_le_add (le_refl (2+(N.primeFactors.card:ℝ)+y)) (chen_square_quotient_sum_bound N z hz))

/-- The integer endpoints in the switching inequality. -/
noncomputable def chenLowerCutoff (N : ℕ) : ℕ := ⌊(N:ℝ)^(1/8:ℝ)⌋₊
noncomputable def chenUpperCutoff (N : ℕ) : ℕ := ⌊(N:ℝ)^(1/3:ℝ)⌋₊

noncomputable def chenElementaryError (N : ℕ) : ℝ :=
  (chenBadSet N (chenLowerCutoff N) (chenUpperCutoff N)).card

theorem floor_cutoff_cube {N : ℕ} (hN : 2^24≤N) :
    N<(chenUpperCutoff N+1)^3 ∧ 3≤chenUpperCutoff N := by
  let s := (N:ℝ)^(1/3:ℝ)
  have hs : 0≤s := by dsimp [s]; positivity
  have h₃ : s^3=(N:ℝ) := by
    dsimp [s]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hlarge : (2:ℝ)^24≤(N:ℝ) := by exact_mod_cast hN
  have hs3 : 3≤s := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h hs (by decide : 3≠0)
    linarith
  have hlt := Nat.lt_floor_add_one s
  have hh := pow_lt_pow_left₀ hlt hs (by decide : 3≠0)
  rw [h₃] at hh
  exact ⟨by exact_mod_cast hh,Nat.le_floor (by exact_mod_cast hs3)⟩

/-- At the floor cutoffs the stated finite correction has the usual Chen order,
with an explicit constant even when all prime complements are admitted. -/
theorem chenElementaryError_le {N : ℕ} (hN : 2^24≤N) :
    chenElementaryError N ≤ 2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ) := by
  let t := (N:ℝ)^(1/8:ℝ)
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  have hN0 : 0<N := by omega
  have hN' : (0:ℝ)<N := by exact_mod_cast hN0
  have ht : 0≤t := by dsimp [t]; positivity
  have ht8 : t^8=(N:ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    norm_num
  have ht7 : t^7=(N:ℝ)^(7/8:ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
    norm_num
  have ht8ge : 8≤t := by
    by_contra! h
    have hh := pow_lt_pow_left₀ h ht (by decide : 8≠0)
    have hlarge : (2:ℝ)^24≤(N:ℝ) := by exact_mod_cast hN
    linarith
  have hzf : t<(z:ℝ)+1 := Nat.lt_floor_add_one t
  have hz₂ : 2≤z := Nat.le_floor (by change (2:ℝ)≤t; linarith)
  have hzpos : 0<(z:ℝ)-1 := by
    have hz' : (2:ℝ)≤z := by exact_mod_cast hz₂
    linarith
  have hratio : (N:ℝ)/((z:ℝ)-1)≤(4/3:ℝ)*t^7 := by
    apply (div_le_iff₀ hzpos).2
    have hden : t ≤ (4/3:ℝ)*((z:ℝ)-1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hden (pow_nonneg ht 7)
    nlinarith only [hmul,ht8]
  have homega := primeFactors_card_le_two_log (M:=N) hN0
  rw [Real.log_mul (by norm_num) hN'.ne'] at homega
  have hlog := Real.log_le_rpow_div hN'.le (by norm_num : (0:ℝ)<1/8)
  change Real.log (N:ℝ) ≤ t/(1/8) at hlog
  have hlog₂ := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hcard : 2+(N.primeFactors.card:ℝ)≤4+16*t := by linarith
  have hp₆ := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤8) ht8ge 6
  have hh := mul_le_mul_of_nonneg_right hp₆ ht
  have hslack : 4+16*t≤(2/3:ℝ)*t^7 := by nlinarith only [hh,ht8ge]
  have hy : (y:ℝ)≤(N:ℝ)^(1/3:ℝ) := Nat.floor_le (by positivity)
  have hb := chenBadSet_card_bound (y:=y) hN0 hz₂
  change ((chenBadSet N z y).card:ℝ) ≤ _
  rw [← ht7]
  linarith only [hb,hratio,hcard,hslack,hy]

/-- Chen's switching inequality at the two integer floors, with the unrestricted
switched carrier and its finite elementary correction. -/
theorem chen_switching_inequality_floor {N : ℕ} (hN : 2^24≤N) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenUnrestrictedB N z y)).card:ℝ) - chenElementaryError N ≤
        (chenCount N:ℝ) := by
  obtain ⟨hy,hy3⟩ := floor_cutoff_cube hN
  exact chen_switching_inequality_unrestricted hy hy3

/-- The concrete power-saving remainder for the floored, unrestricted formulation. -/
theorem chen_switching_inequality_floor_explicit {N : ℕ} (hN : 2^24≤N) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenUnrestrictedB N z y)).card:ℝ) -
      (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤ (chenCount N:ℝ) := by
  exact (sub_le_sub_left (chenElementaryError_le hN) _).trans (chen_switching_inequality_floor hN)

/-- The explicit floored switching bound for rough, squarefree Chen representations. -/
theorem chen_switching_inequality_floor_rough_explicit {N : ℕ} (hN : 2^24≤N) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenUnrestrictedB N z y)).card:ℝ) -
      (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤ ((chenRoughRepresentations N z).card:ℝ) := by
  obtain ⟨hy, hy3⟩ := floor_cutoff_cube hN
  exact (sub_le_sub_left (chenElementaryError_le hN) _).trans
    (chen_switching_inequality_rough_unrestricted hy hy3)

end FareyGoldbach
