import FareyGoldbach.PrimitiveLargeSieve

/-! # Character expansion of ordered products by conductor -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- A primitive character evaluated after removing the factors sharing primes with the cofactor. -/
noncomputable def chenMaskedChar {q : ℕ} (ψ : DirichletCharacter ℂ q) (k n : ℕ) : ℂ :=
  if n.Coprime k then ψ (n : ZMod q) else 0

/-- Primitive first moment with the same cofactor mask on both variables of the pair sum. -/
noncomputable def chenMaskedPrimitiveMass (P : Finset (ℕ × ℕ)) (q k : ℕ) : ℝ :=
  if h : 0 < q then
    letI : NeZero q := ⟨h.ne'⟩
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.IsPrimitive),
      ‖∑ x ∈ P, chenMaskedChar ψ k x.1 * chenMaskedChar ψ k x.2‖
  else 0

theorem chenMaskedPrimitiveMass_of_pos (P : Finset (ℕ × ℕ)) {q : ℕ} [NeZero q] (k : ℕ) :
    chenMaskedPrimitiveMass P q k =
    ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.IsPrimitive),
      ‖∑ x ∈ P, chenMaskedChar ψ k x.1 * chenMaskedChar ψ k x.2‖ := by
  simp [chenMaskedPrimitiveMass, NeZero.pos q]

theorem chenMaskedPrimitiveMass_nonneg (P : Finset (ℕ × ℕ)) (q k : ℕ) :
    0 ≤ chenMaskedPrimitiveMass P q k := by
  unfold chenMaskedPrimitiveMass
  split
  · exact sum_nonneg fun _ _ => norm_nonneg _
  · rfl

/-- The cofactor mask accounts for all new nonunits when the level is enlarged. -/
theorem chenChangeLevel_apply_mask {q d : ℕ} (hqd : q ∣ d) (ψ : DirichletCharacter ℂ q)
    (n : ℕ) :
    ψ.changeLevel hqd (n : ZMod d) = chenMaskedChar ψ (d/q) n := by
  have hfac : n.Coprime d ↔ n.Coprime q ∧ n.Coprime (d/q) := by
    rw [← Nat.coprime_mul_iff_right, Nat.mul_div_cancel' hqd]
  by_cases hc : n.Coprime (d/q)
  · rw [chenMaskedChar, ite_eq_left hc]
    by_cases hq : n.Coprime q
    · have hd := hfac.mpr ⟨hq,hc⟩
      simpa using DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hqd
        (Nat.isCoprime_iff_coprime.mpr hd)
    · have hd : ¬n.Coprime d := fun h => hq (hfac.mp h).1
      rw [MulChar.map_nonunit _ (fun hu => hd ((ZMod.isUnit_iff_coprime n d).mp hu)),
        MulChar.map_nonunit _ (fun hu => hq ((ZMod.isUnit_iff_coprime n q).mp hu))]
  · have hd : ¬n.Coprime d := fun h => hc (hfac.mp h).2
    simp [chenMaskedChar,hc,MulChar.map_nonunit _ (fun hu => hd ((ZMod.isUnit_iff_coprime n d).mp hu))]

theorem chenConductorFiber_eq_image {q d : ℕ} [NeZero d] [NeZero q] (hqd : q ∣ d) :
    (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.conductor=q) =
    ((univ : Finset (DirichletCharacter ℂ q)).filter (fun ψ => ψ.IsPrimitive)).image
      (DirichletCharacter.changeLevel (R:=ℂ) hqd) := by
  classical
  ext χ
  simp only [mem_filter,mem_univ,true_and,mem_image]
  constructor
  · intro h
    subst q
    exact ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩
  · rintro ⟨ψ,hψ,rfl⟩
    exact (ψ.conductor_changeLevel hqd).trans hψ

private theorem chen_conductor_fiber_sum (P : Finset (ℕ × ℕ)) {q d : ℕ}
    [NeZero d] [NeZero q] (hqd : q ∣ d) :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.conductor=q),
      ‖∑ x ∈ P, χ ((x.1*x.2 : ℕ) : ZMod d)‖) = chenMaskedPrimitiveMass P q (d/q) := by
  classical
  rw [chenConductorFiber_eq_image hqd, sum_image (fun _ _ _ _ h => DirichletCharacter.changeLevel_injective hqd h),
    chenMaskedPrimitiveMass_of_pos]
  refine sum_congr rfl fun ψ _ => congrArg norm ?_
  refine sum_congr rfl fun x _ => ?_
  rw [Nat.cast_mul,map_mul,chenChangeLevel_apply_mask,chenChangeLevel_apply_mask]

/-- Exact conductor grouping, with the principal character removed before the grouping. -/
theorem chenNonprincipal_sum_eq_conductors (P : Finset (ℕ × ℕ)) {d : ℕ} [NeZero d] :
    (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ≠1),
      ‖∑ x ∈ P, χ ((x.1*x.2 : ℕ) : ZMod d)‖) =
    ∑ q ∈ d.divisors.filter (fun q => 1<q), chenMaskedPrimitiveMass P q (d/q) := by
  classical
  let S := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ≠1)
  let Q := d.divisors.filter (fun q => 1<q)
  have hmap (χ : DirichletCharacter ℂ d) (hχ : χ ∈ S) : χ.conductor ∈ Q := by
    have hc := (mem_filter.mp hχ).2
    have hne := mt (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=χ)).mpr hc
    have hpos := Nat.pos_of_ne_zero χ.conductor_ne_zero
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level,NeZero.ne d⟩,by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply sum_congr rfl
  intro q hq
  obtain ⟨hqdiv,hq1⟩ := mem_filter.mp hq
  let : NeZero q := ⟨by omega⟩
  have hf : S.filter (fun χ => χ.conductor=q) =
      (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ.conductor=q) := by
    ext χ
    simp only [S,mem_filter,mem_univ,true_and]
    exact ⟨And.right, fun he => ⟨fun hh => by
      have := (DirichletCharacter.eq_one_iff_conductor_eq_one (χ:=χ)).mp hh
      omega, he⟩⟩
  rw [hf]
  exact chen_conductor_fiber_sum P (Nat.mem_divisors.mp hqdiv).1

private theorem chenPair_fourier {d a : ℕ} [NeZero d] (ha : a.Coprime d)
    (P : Finset (ℕ × ℕ)) :
    (∑ χ : DirichletCharacter ℂ d, χ (a : ZMod d)⁻¹ *
      ∑ x ∈ P, χ ((x.1*x.2 : ℕ) : ZMod d)) =
      (d.totient:ℂ) * ((P.filter (fun x => (x.1*x.2)%d=a%d)).card:ℂ) := by
  classical
  have hu := (ZMod.isUnit_iff_coprime a d).mpr ha
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ P, (if (x.1*x.2)%d=a%d then (d.totient:ℂ) else 0) := by
      refine sum_congr rfl fun x _ => ?_
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu]
      by_cases h : (x.1*x.2)%d=a%d
      · rw [ite_eq_left ((ZMod.natCast_eq_natCast_iff' a _ d).2 h.symm), ite_eq_left h]
      · have hz : (a:ZMod d) ≠ ((x.1*x.2:ℕ):ZMod d) :=
          fun hz => h ((ZMod.natCast_eq_natCast_iff' a _ d).1 hz).symm
        rw [ite_eq_right hz, ite_eq_right h]
    _ = _ := by rw [← Finset.sum_filter]; simp [nsmul_eq_mul,mul_comm]

private theorem chenPair_principal_sum (P : Finset (ℕ × ℕ)) {d : ℕ} [NeZero d] :
    (∑ x ∈ P, (1 : DirichletCharacter ℂ d) ((x.1*x.2 : ℕ) : ZMod d)) =
    ((P.filter (fun x => (x.1*x.2).Coprime d)).card:ℂ) := by
  classical
  have hf (x : ℕ×ℕ) : (1 : DirichletCharacter ℂ d) ((x.1*x.2 : ℕ) : ZMod d) =
      if (x.1*x.2).Coprime d then 1 else 0 := by
    by_cases h : (x.1*x.2).Coprime d
    · rw [ite_eq_left h]
      exact MulChar.one_apply ((ZMod.isUnit_iff_coprime _ d).mpr h)
    · rw [ite_eq_right h]
      exact MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime _ d).mp hu))
  simp_rw [hf]
  rw [← Finset.sum_filter]
  simp

/-- AP discrepancy for an arbitrary finite set of ordered pairs. The principal term
counts products with a nontrivial common factor with the modulus. -/
theorem chenPairAP_discrepancy_le_raw (P : Finset (ℕ × ℕ)) {d a : ℕ}
    (hd : 0<d) (ha : a.Coprime d) :
    |((P.filter (fun x => (x.1*x.2)%d=a%d)).card:ℝ) - (P.card:ℝ)/(d.totient:ℝ)| ≤
    (((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ) +
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ d)).filter (·≠1), ‖∑ x ∈ P, χ ((x.1*x.2 : ℕ) : ZMod d)‖)/(d.totient:ℝ) := by
  classical
  let : NeZero d := ⟨hd.ne'⟩
  let φ : ℝ := d.totient
  let A := P.filter (fun x => (x.1*x.2)%d=a%d)
  let B := P.filter (fun x => ¬(x.1*x.2).Coprime d)
  let G := P.filter (fun x => (x.1*x.2).Coprime d)
  let V (χ : DirichletCharacter ℂ d) := ∑ x ∈ P, χ ((x.1*x.2:ℕ):ZMod d)
  let W (χ : DirichletCharacter ℂ d) := χ (a:ZMod d)⁻¹ * V χ
  let S := (univ : Finset (DirichletCharacter ℂ d)).filter (fun χ => χ≠1)
  have hφ : 0<φ := Nat.cast_pos.mpr (Nat.totient_pos.mpr hd)
  have hφc : (φ:ℂ)≠0 := by exact_mod_cast hφ.ne'
  have hu := (ZMod.isUnit_iff_coprime a d).mpr ha
  have hau : IsUnit ((a:ZMod d)⁻¹) := by
    have h : IsUnit ((a:ℤ):ZMod d) := by exact_mod_cast hu
    simpa only [Int.cast_natCast] using ZMod.isUnit_inv h
  have hprin : W 1 = (G.card:ℂ) := by
    dsimp only [W,V,G]
    rw [MulChar.one_apply hau,one_mul,chenPair_principal_sum]
  have htotal : (∑ χ : DirichletCharacter ℂ d, W χ)=(φ:ℂ)*(A.card:ℂ) := by
    simpa only [W,V,A,φ,Complex.ofReal_natCast] using chenPair_fourier ha P
  have hS : S = univ.erase 1 := by ext χ; simp [S]
  have hsplit : (∑ χ∈S,W χ) + (G.card:ℂ) = (φ:ℂ)*(A.card:ℂ) := by
    rw [hS, ← hprin, Finset.sum_erase_add _ _ (mem_univ _), htotal]
  have hcards : (G.card:ℂ)+(B.card:ℂ)=(P.card:ℂ) := by
    exact_mod_cast @Finset.card_filter_add_card_filter_not _ P (fun x => (x.1*x.2).Coprime d) _ _
  have hident : (φ:ℂ)*((A.card:ℂ)-(P.card:ℂ)/(φ:ℂ)) =
      (∑ χ∈S,W χ)-(B.card:ℂ) := by
    rw [mul_sub, show (φ:ℂ)*((P.card:ℂ)/(φ:ℂ))=(P.card:ℂ) by field_simp,
      ← hcards, ← hsplit]
    ring
  have hnorm : ‖∑ χ∈S,W χ‖ ≤ ∑ χ∈S,‖V χ‖ := by
    apply (norm_sum_le _ _).trans
    refine sum_le_sum fun χ _ => ?_
    dsimp only [W]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  apply (le_div_iff₀ hφ).mpr
  change |(A.card:ℝ)-(P.card:ℝ)/φ| * φ ≤ (B.card:ℝ) + _
  rw [mul_comm]
  calc
    _ = ‖(φ:ℂ)*((A.card:ℂ)-(P.card:ℂ)/(φ:ℂ))‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hφ,← Real.norm_eq_abs,← Complex.norm_real]
      push_cast
      rfl
    _ = ‖(∑ χ∈S,W χ)-(B.card:ℂ)‖ := by rw [hident]
    _ ≤ _ := norm_sub_le _ _
    _ ≤ (B.card:ℝ) + ∑ χ∈S,‖V χ‖ := by simpa [add_comm] using add_le_add_right hnorm ‖(B.card:ℂ)‖

theorem chenPairAP_discrepancy_le (P : Finset (ℕ × ℕ)) {d a : ℕ}
    (hd : 0<d) (ha : a.Coprime d) :
    |((P.filter (fun x => (x.1*x.2)%d=a%d)).card:ℝ) - (P.card:ℝ)/(d.totient:ℝ)| ≤
    (((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ) +
      ∑ q ∈ d.divisors.filter (fun q => 1<q), chenMaskedPrimitiveMass P q (d/q))/(d.totient:ℝ) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  have h := chenPairAP_discrepancy_le_raw P hd ha
  rw [chenNonprincipal_sum_eq_conductors] at h
  exact h
/-- Regroup the divisor sum by the cofactor while keeping the original strict product cutoff. -/
theorem chenSum_divisors_swap (D : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ d ∈ Ico 1 D, ∑ q ∈ d.divisors.filter (fun q => 1<q), F q (d/q)) =
      ∑ k ∈ Ico 1 D, ∑ q ∈ (Ico 2 D).filter (fun q => k*q<D), F q k := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine sum_bij' (fun p _ => ⟨p.1/p.2,p.2⟩) (fun p _ => ⟨p.1*p.2,p.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d,q⟩ hp
    obtain ⟨hd,hq⟩ := mem_sigma.mp hp
    change d ∈ Ico 1 D at hd
    change q ∈ d.divisors.filter (fun q => 1<q) at hq
    obtain ⟨hd1,hdD⟩ := mem_Ico.mp hd
    obtain ⟨hqdiv,hq2⟩ := mem_filter.mp hq
    have hqd := (Nat.mem_divisors.mp hqdiv).1
    have hqle := Nat.le_of_dvd (by omega : 0<d) hqd
    have hpos := Nat.div_pos hqle (by omega)
    have hkD := (Nat.div_le_self d q).trans_lt hdD
    have hprod := Nat.div_mul_cancel hqd
    exact mem_sigma.mpr ⟨mem_Ico.mpr ⟨hpos,hkD⟩,mem_filter.mpr
      ⟨mem_Ico.mpr ⟨hq2,hqle.trans_lt hdD⟩,hprod.trans_lt hdD⟩⟩
  · rintro ⟨k,q⟩ hp
    obtain ⟨hk,hq⟩ := mem_sigma.mp hp
    change k ∈ Ico 1 D at hk
    change q ∈ (Ico 2 D).filter (fun q => k*q<D) at hq
    obtain ⟨hk1,_⟩ := mem_Ico.mp hk
    obtain ⟨hqI,hprod⟩ := mem_filter.mp hq
    have hq2 := (mem_Ico.mp hqI).1
    have hpos : 0<k*q := Nat.mul_pos (by omega) (by omega)
    exact mem_sigma.mpr ⟨mem_Ico.mpr ⟨hpos,hprod⟩,mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.dvd_mul_left q k, hpos.ne'⟩,hq2⟩⟩
  · rintro ⟨d,q⟩ hp
    have hqd := (Nat.mem_divisors.mp (mem_filter.mp (mem_sigma.mp hp).2).1).1
    exact congrArg (fun n : ℕ => (⟨n,q⟩ : Σ _ : ℕ, ℕ)) (Nat.div_mul_cancel hqd)
  · rintro ⟨k,q⟩ hp
    have hq2 : 2 ≤ q := (mem_Ico.mp (mem_filter.mp (mem_sigma.mp hp).2).1).1
    exact congrArg (fun n : ℕ => (⟨n,q⟩ : Σ _ : ℕ, ℕ)) (Nat.mul_div_cancel k (by omega : 0<q))
  · intro _ _
    rfl

/-- Once the cofactor is fixed, the same masked coefficients may be used for every
primitive conductor in the inner sum. -/
theorem chenConductorMass_sum_le (P : Finset (ℕ × ℕ)) (a D : ℕ) :
    (∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime a),
      (∑ q ∈ d.divisors.filter (fun q => 1<q), chenMaskedPrimitiveMass P q (d/q))/(d.totient:ℝ)) ≤
    ∑ k ∈ Ico 1 D, (1/(k.totient:ℝ)) *
      ∑ q ∈ Ico 2 D, chenMaskedPrimitiveMass P q k/(q.totient:ℝ) := by
  classical
  calc
    _ ≤ ∑ d ∈ Ico 1 D,
        (∑ q ∈ d.divisors.filter (fun q => 1<q), chenMaskedPrimitiveMass P q (d/q))/(d.totient:ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset ..)
      intro d _ _
      exact div_nonneg (sum_nonneg fun q _ => chenMaskedPrimitiveMass_nonneg ..) (Nat.cast_nonneg _)
    _ = ∑ d ∈ Ico 1 D, ∑ q ∈ d.divisors.filter (fun q => 1<q),
        chenMaskedPrimitiveMass P q (d/q)/((d/q*q).totient:ℝ) := by
      refine sum_congr rfl fun d _ => ?_
      rw [Finset.sum_div]
      refine sum_congr rfl fun q hq => ?_
      rw [Nat.div_mul_cancel (Nat.mem_divisors.mp (mem_filter.mp hq).1).1]
    _ = _ := chenSum_divisors_swap D (fun q k => chenMaskedPrimitiveMass P q k/((k*q).totient:ℝ))
    _ ≤ _ := by
      refine sum_le_sum fun k hk => ?_
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ q ∈ (Ico 2 D).filter (fun q => k*q<D),
            (1/(k.totient:ℝ))*(chenMaskedPrimitiveMass P q k/(q.totient:ℝ)) := by
          refine sum_le_sum fun q hq => ?_
          have hk1 := (mem_Ico.mp hk).1
          have hq2 := (mem_Ico.mp (mem_filter.mp hq).1).1
          have hφk : (0:ℝ) < k.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
          have hφq : (0:ℝ) < q.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
          have hden : (k.totient:ℝ)*(q.totient:ℝ) ≤ ((k*q).totient:ℝ) := by
            exact_mod_cast Nat.totient_super_multiplicative k q
          apply (div_le_div_of_nonneg_left (chenMaskedPrimitiveMass_nonneg ..) (mul_pos hφk hφq) hden).trans
          exact le_of_eq (by ring)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) fun q _ _ =>
          mul_nonneg (by positivity) (div_nonneg (chenMaskedPrimitiveMass_nonneg ..) (Nat.cast_nonneg _))

theorem chenPairAP_sum_le (P : Finset (ℕ × ℕ)) (a D : ℕ) :
    (∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime a),
      |((P.filter (fun x => (x.1*x.2)%d=a%d)).card:ℝ) - (P.card:ℝ)/(d.totient:ℝ)|) ≤
    (∑ d ∈ (Ico 1 D).filter (fun d => d.Coprime a),
      ((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ)/(d.totient:ℝ)) +
    ∑ k ∈ Ico 1 D, (1/(k.totient:ℝ)) *
      ∑ q ∈ Ico 2 D, chenMaskedPrimitiveMass P q k/(q.totient:ℝ) := by
  classical
  have h := sum_le_sum (s:=(Ico 1 D).filter (fun d => d.Coprime a))
    (fun d hd => chenPairAP_discrepancy_le P (mem_Ico.mp (mem_filter.mp hd).1).1 (mem_filter.mp hd).2.symm)
  simp_rw [add_div] at h
  rw [sum_add_distrib] at h
  exact h.trans (add_le_add_right (chenConductorMass_sum_le P a D) _)

end FareyGoldbach
