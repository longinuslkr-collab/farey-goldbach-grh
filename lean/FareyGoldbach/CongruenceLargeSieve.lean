import FareyGoldbach.PrimitiveLargeSieve

/-! # Large sieve for moduli divisible by a fixed integer

For denominators `r₁*q` and `r₁*s`, the cross difference has denominator
`r₁*q*s`. Reducedness gives a nonzero integer numerator at distinct centers.
-/

open scoped Classical

namespace FareyGoldbach

private lemma multiple_frequency_gap {r Q q s b c : ℕ} (hr : 0 < r)
    (hq : q ∈ Finset.Icc 1 Q) (hs : s ∈ Finset.Icc 1 Q)
    (hb : b ∈ coprimeClasses (r*q)) (hc : c ∈ coprimeClasses (r*s))
    (hne : ¬ (q=s ∧ b=c)) :
    1/((r:ℝ)*(Q:ℝ)^2) ≤ |(b:ℝ)/((r:ℝ)*q) - (c:ℝ)/((r:ℝ)*s)| := by
  obtain ⟨hq₁,hqQ⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hs₁,hsQ⟩ := Finset.mem_Icc.mp hs
  have hbq : Nat.Coprime b q := (Nat.coprime_mul_iff_right.mp (mem_coprimeClasses.mp hb).2).2
  have hcs : Nat.Coprime c s := (Nat.coprime_mul_iff_right.mp (mem_coprimeClasses.mp hc).2).2
  let k : ℤ := (b:ℤ)*s - (c:ℤ)*q
  have hk : k ≠ 0 := by
    intro h0
    have hz : (b:ℤ)*s=(c:ℤ)*q := sub_eq_zero.mp h0
    have he : b*s=c*q := by exact_mod_cast hz
    have hqs : q ∣ s := hbq.symm.dvd_of_dvd_mul_left ⟨c,by rw [he,Nat.mul_comm]⟩
    have hsq : s ∣ q := hcs.symm.dvd_of_dvd_mul_left ⟨b,by rw [←he,Nat.mul_comm]⟩
    have h := Nat.dvd_antisymm hqs hsq
    subst s
    exact hne ⟨rfl,Nat.eq_of_mul_eq_mul_right hq₁ he⟩
  have hk₁ : (1:ℝ) ≤ |(k:ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hr' : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hq' : 0 < (q:ℝ) := Nat.cast_pos.mpr hq₁
  have hs' : 0 < (s:ℝ) := Nat.cast_pos.mpr hs₁
  have hid : (b:ℝ)/((r:ℝ)*q)-(c:ℝ)/((r:ℝ)*s) = (k:ℝ)/((r:ℝ)*(q:ℝ)*(s:ℝ)) := by
    dsimp only [k]
    push_cast
    field_simp
  rw [hid,abs_div,abs_of_pos (by positivity : 0<(r:ℝ)*(q:ℝ)*(s:ℝ))]
  apply (one_div_le_one_div_of_le (by positivity) ?_).trans
    (div_le_div_of_nonneg_right hk₁ (by positivity))
  rw [mul_assoc,pow_two]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (Nat.cast_le.mpr hqQ) (Nat.cast_le.mpr hsQ) hs'.le (Nat.cast_nonneg _)) hr'.le

/-- The additive large sieve on the denominators `r₁*q`, for `1 ≤ q ≤ Q`. -/
theorem additive_large_sieve_multiple (r₁ M N Q : ℕ) (hr₁ : 0 < r₁) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ b ∈ coprimeClasses (r₁*q),
      ‖∑ n ∈ Finset.Ioc M (M+N), a n * e ((n:ℝ)*b/(r₁*q:ℕ))‖^2) ≤
      50*((N:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*(∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
  by_cases hQ : Q=0
  · subst Q
    simp
    positivity
  have hQ' : (0:ℝ)<Q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ)
  let S := (Finset.Icc 1 Q).sigma (fun q => coprimeClasses (r₁*q))
  let x (i : (_ : ℕ) × ℕ) := (i.2:ℝ)/((r₁:ℝ)*i.1)
  have h0 (i) (_ : i ∈ S) : 0 ≤ x i := by dsimp [x]; positivity
  have h1 (i) (hi : i ∈ S) : x i + 1/((r₁:ℝ)*(Q:ℝ)^2) ≤ 1 := by
    obtain ⟨hiq,hib⟩ := Finset.mem_sigma.mp hi
    obtain ⟨hq₁,hqQ⟩ := Finset.mem_Icc.mp hiq
    have ha : (i.2:ℝ)+1 ≤ (r₁:ℝ)*i.1 := by exact_mod_cast (mem_coprimeClasses.mp hib).1
    have hq : (0:ℝ) < i.1 := Nat.cast_pos.mpr hq₁
    have hQQ : (Q:ℝ) ≤ (Q:ℝ)^2 := by
      have h : (1:ℝ) ≤ Q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hQ)
      nlinarith only [mul_nonneg (sub_nonneg.mpr h) hQ'.le]
    have hden : (r₁:ℝ)*(i.1:ℝ) ≤ (r₁:ℝ)*(Q:ℝ)^2 :=
      mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr hqQ).trans hQQ) (Nat.cast_nonneg _)
    have hpos : 0 < (r₁:ℝ)*i.1 := by positivity
    calc x i+1/((r₁:ℝ)*(Q:ℝ)^2) ≤ x i+1/((r₁:ℝ)*i.1) :=
           add_le_add_right (one_div_le_one_div_of_le hpos hden) _
         _ = ((i.2:ℝ)+1)/((r₁:ℝ)*i.1) := (add_div ..).symm
         _ ≤ 1 := (div_le_one hpos).mpr ha
  have hsep (i) (hi : i ∈ S) (j) (hj : j ∈ S) (hne : i ≠ j) :
      1/((r₁:ℝ)*(Q:ℝ)^2) ≤ |x i-x j| := by
    obtain ⟨hiq,hib⟩ := Finset.mem_sigma.mp hi
    obtain ⟨hjq,hjb⟩ := Finset.mem_sigma.mp hj
    apply multiple_frequency_gap hr₁ hiq hjq hib hjb
    rintro ⟨h₁,h₂⟩
    exact hne (Sigma.ext h₁ (heq_of_eq h₂))
  have h := separated_large_sieve S x (by positivity : 0<(r₁:ℝ)*(Q:ℝ)^2) h0 h1 hsep M N a
  simpa only [S,x,Finset.sum_sigma',Nat.cast_mul,←mul_div_assoc] using h

/-- The primitive-character large sieve on the same moduli, including the weight
`r₁*q/φ(r₁*q)` in `primitiveCharacterEnergy`. -/
theorem primitive_large_sieve_multiple (r₁ M N Q : ℕ) (hr₁ : 0 < r₁) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, primitiveCharacterEnergy (r₁*q) (Finset.Ioc M (M+N)) a) ≤
      50*((N:ℝ)+(r₁:ℝ)*(Q:ℝ)^2)*(∑ n ∈ Finset.Ioc M (M+N), ‖a n‖^2) := by
  apply le_trans _ (additive_large_sieve_multiple r₁ M N Q hr₁ a)
  exact Finset.sum_le_sum fun q hq =>
    primitiveCharacterEnergy_le_additive (Nat.mul_pos hr₁ (Finset.mem_Icc.mp hq).1) _ a

end FareyGoldbach
