import FareyGoldbach.RoughGoldbachLowerSieve

/-! # Finite Chen switching with a fourth-root upper cutoff -/

namespace FareyGoldbach

open scoped Classical

/-- Reflections of strictly ordered triples with every prime at least `y`. -/
noncomputable def chenQuarterB30 (N y : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun b ↦ ∃ u v w : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧ y≤u ∧ u<v ∧ v<w ∧ u*v*w<N ∧ b=N-u*v*w

/-- Reflections of strictly ordered triples with one prime in `[z,y)`. -/
noncomputable def chenQuarterB31 (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun b ↦ ∃ u v w : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧ z≤u ∧ u<y ∧ y≤v ∧ v<w ∧ u*v*w<N ∧ b=N-u*v*w

/-- Reflections of strictly ordered quadruples with one prime in `[z,y)`. -/
noncomputable def chenQuarterB41 (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun b ↦ ∃ u v w t : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧ t.Prime ∧ z≤u ∧ u<y ∧ y≤v ∧ v<w ∧ w<t ∧
      u*v*w*t<N ∧ b=N-u*v*w*t

/-- Distinct odd primes at and beyond the fourth-root cutoff are spaced by at least two. -/
theorem chen_quarter_four_large_primes {N y u v w t : ℕ} (hy : N<(y+1)^4)
    (hy3 : 3≤y) (hu : u.Prime) (hv : v.Prime) (hw : w.Prime) (ht : t.Prime)
    (hyu : y≤u) (huv : u<v) (hvw : v<w) (hwt : w<t) : N<u*v*w*t := by
  obtain ⟨a,ha⟩ := hu.odd_iff.mpr (by omega)
  obtain ⟨b,hb⟩ := hv.odd_iff.mpr (by omega)
  obtain ⟨c,hc⟩ := hw.odd_iff.mpr (by omega)
  obtain ⟨d,hd⟩ := ht.odd_iff.mpr (by omega)
  have hv' : y+2≤v := by omega
  have hw' : y+4≤w := by omega
  have ht' : y+6≤t := by omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hyu hv') hw') ht'
  have hpair : (y+1)^2≤y*(y+4) := by
    exact_mod_cast (show ((y:ℤ)+1)^2≤(y:ℤ)*((y:ℤ)+4) by
      have hy' : (3:ℤ)≤y := by exact_mod_cast hy3
      nlinarith only [hy'])
  have hpair' : (y+1)^2≤(y+2)*(y+6) := by
    simpa only [pow_two] using Nat.mul_le_mul (show y+1≤y+2 by omega) (show y+1≤y+6 by omega)
  refine hy.trans_le ((?_ : (y+1)^4≤y*(y+2)*(y+4)*(y+6)).trans hmul)
  calc
    _ = (y+1)^2 * (y+1)^2 := by ring
    _ ≤ (y*(y+4))*((y+2)*(y+6)) := Nat.mul_le_mul hpair hpair'
    _ = _ := by ac_rfl

/-- Pointwise quarter-cutoff switching. Two medium prime factors pay the full charge,
even if the complement has more than four prime factors. -/
theorem chen_quarter_two_charges {N z y a : ℕ} (hy : N<(y+1)^4) (hy3 : 3≤y)
    (ha : a ∈ chenSifted N z (chenA N)) :
    2 ≤ 2*(if a ∈ chenRoughRepresentations N z then 1 else 0) +
      ((chenMediumPrimes z y).filter (· ∣ a)).card +
      2*(if N-a ∈ chenSifted N y (chenQuarterB30 N y) then 1 else 0) +
      (if N-a ∈ chenSifted N y (chenQuarterB31 N z y) then 1 else 0) +
      (if N-a ∈ chenSifted N y (chenQuarterB41 N z y) then 1 else 0) +
      2*(if a ∈ chenBadSet N z y then 1 else 0) := by
  classical
  by_cases hb : a ∈ chenBadSet N z y
  · simp only [ite_eq_left hb]
    omega
  have hclean : a ∈ chenRoughThreeClean N z y := Finset.mem_sdiff.mpr ⟨ha,hb⟩
  obtain ⟨haN,hp,ha2,hsq,hcop,hrough,hpy⟩ := mem_chenRoughThreeClean_iff.mp hclean
  have ha0 : 0<a := by omega
  have ha_lt : a<N := by have := hp.pos; omega
  have hrfl : chenRough N y (N-a) := by
    intro q hq hqp _ hd
    have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hd
    have hqy := Finset.mem_range.mp hq
    omega
  by_cases hap : IsAlmostPrimeTwo a
  · have hgood : a∈chenRoughRepresentations N z :=
      mem_chenRoughRepresentations_iff.mpr ⟨N-a,hp,hap,ha2,hsq,hcop,hrough,Nat.sub_add_cancel haN⟩
    simp only [ite_eq_left hgood]
    omega
  have hlen : ¬a.primeFactorsList.length≤2 :=
    fun h ↦ hap ((isAlmostPrimeTwo_iff_primeFactorsList_length_le_two ha0).mpr h)
  have hprod := Nat.prod_primeFactorsList ha0.ne'
  have hsort := ((Nat.primeFactorsList_sorted a).sortedLT_of_nodup hsq.nodup_primeFactorsList).pairwise
  have hmedium {q : ℕ} (hq : q∈a.primeFactorsList) (hqy : q<y) :
      q∈(chenMediumPrimes z y).filter (· ∣ a) := by
    have hqz := hrough q (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hq)
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hqz,hqy⟩,Nat.prime_of_mem_primeFactorsList hq⟩,
      Nat.dvd_of_mem_primeFactorsList hq⟩
  rcases hL : a.primeFactorsList with _ | ⟨u,_ | ⟨v,_ | ⟨w,ws⟩⟩⟩
  · cases (by simp [hL] at hlen : False)
  · cases (by simp [hL] at hlen : False)
  · cases (by simp [hL] at hlen : False)
  have hu : u∈a.primeFactorsList := by simp [hL]
  have hv : v∈a.primeFactorsList := by simp [hL]
  have hw : w∈a.primeFactorsList := by simp [hL]
  have huP := Nat.prime_of_mem_primeFactorsList hu
  have hvP := Nat.prime_of_mem_primeFactorsList hv
  have hwP := Nat.prime_of_mem_primeFactorsList hw
  have huz := hrough u (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hu)
  rw [hL] at hsort hprod
  obtain ⟨huL, hsort⟩ := List.pairwise_cons.mp hsort
  obtain ⟨hvL, hsort⟩ := List.pairwise_cons.mp hsort
  obtain ⟨hwL, hsort⟩ := List.pairwise_cons.mp hsort
  have huv : u<v := huL v (by simp)
  have hvw : v<w := hvL w (by simp)
  by_cases hvy : v<y
  · have htwo : 2 ≤ ((chenMediumPrimes z y).filter (· ∣ a)).card :=
      Finset.Nontrivial.two_le_card ⟨u,hmedium hu (huv.trans hvy),v,hmedium hv hvy,huv.ne⟩
    omega
  have hyv : y≤v := by omega
  cases ws with
  | nil =>
    have heq : a=u*v*w := by simpa [mul_assoc] using hprod.symm
    by_cases huy : u<y
    · have hmem : N-a∈chenSifted N y (chenQuarterB31 N z y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega),u,v,w,huP,hvP,hwP,huz,huy,hyv,hvw,
            heq ▸ ha_lt,by rw [heq]⟩, hrfl⟩
      have hone := Finset.card_pos.mpr ⟨u,hmedium hu huy⟩
      simp only [ite_eq_left hmem]
      omega
    · have hmem : N-a∈chenSifted N y (chenQuarterB30 N y) :=
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega),u,v,w,huP,hvP,hwP,by omega,huv,hvw,
            heq ▸ ha_lt,by rw [heq]⟩, hrfl⟩
      simp only [ite_eq_left hmem]
      omega
  | cons t ts =>
    have ht : t∈a.primeFactorsList := by simp [hL]
    have htP := Nat.prime_of_mem_primeFactorsList ht
    have hwt : w<t := hwL t (by simp)
    have huy : u<y := by
      by_contra! h
      have hlarge := chen_quarter_four_large_primes hy hy3 huP hvP hwP htP h huv hvw hwt
      have hdvd : u*v*w*t ∣ a := ⟨ts.prod,by rw [←hprod]; simp only [List.prod_cons]; ac_rfl⟩
      exact hlarge.not_ge ((Nat.le_of_dvd ha0 hdvd).trans haN)
    have hts : ts=[] := by
      cases ts with
      | nil => rfl
      | cons r rs =>
        exfalso
        have hr : r∈a.primeFactorsList := by simp [hL]
        have htr : t<r := (List.pairwise_cons.mp hsort).1 r (by simp)
        have hlarge := chen_quarter_four_large_primes hy hy3 hvP hwP htP
          (Nat.prime_of_mem_primeFactorsList hr) hyv hvw hwt htr
        have hdvd : v*w*t*r ∣ a :=
          ⟨u*rs.prod,by rw [←hprod]; simp only [List.prod_cons]; ac_rfl⟩
        exact hlarge.not_ge ((Nat.le_of_dvd ha0 hdvd).trans haN)
    have heq : a=u*v*w*t := by simpa [hts,mul_assoc] using hprod.symm
    have hmem : N-a∈chenSifted N y (chenQuarterB41 N z y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega),u,v,w,t,huP,hvP,hwP,htP,huz,huy,hyv,hvw,hwt,
          heq ▸ ha_lt,by rw [heq]⟩, hrfl⟩
    have hone := Finset.card_pos.mpr ⟨u,hmedium hu huy⟩
    simp only [ite_eq_left hmem]
    omega

private theorem reflected_card_le (N z : ℕ) (B : Finset ℕ) :
    ((chenSifted N z (chenA N)).filter (fun a ↦ N-a∈B)).card ≤ B.card := by
  classical
  apply Finset.card_le_card_of_injOn (fun a ↦ N-a) (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  intro a ha b hb h
  have ha' := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1
  have hb' := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
  change N-a=N-b at h
  omega

private theorem chen_quarter_switching_twice {N z y : ℕ} (hy : N<(y+1)^4) (hy3 : 3≤y) :
    2*(chenSifted N z (chenA N)).card ≤ 2*(chenRoughRepresentations N z).card +
      (∑ q ∈ chenMediumPrimes z y, (chenSifted N z (chenDivisible (chenA N) q)).card) +
      2*(chenSifted N y (chenQuarterB30 N y)).card +
      (chenSifted N y (chenQuarterB31 N z y)).card +
      (chenSifted N y (chenQuarterB41 N z y)).card + 2*(chenBadSet N z y).card := by
  classical
  let A := chenSifted N z (chenA N)
  have hs := Finset.sum_le_sum (s:=A) (fun a ha ↦ chen_quarter_two_charges hy hy3 ha)
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Nat.cast_id] at hs
  have hGood : (A.filter (· ∈ chenRoughRepresentations N z)).card ≤ (chenRoughRepresentations N z).card :=
    Finset.card_le_card (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  have hBad : (A.filter (· ∈ chenBadSet N z y)).card ≤ (chenBadSet N z y).card :=
    Finset.card_le_card (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  have h30 := reflected_card_le N z (chenSifted N y (chenQuarterB30 N y))
  have h31 := reflected_card_le N z (chenSifted N y (chenQuarterB31 N z y))
  have h41 := reflected_card_le N z (chenSifted N y (chenQuarterB41 N z y))
  have hInc := chen_sifted_incident_sum N z y (chenA N)
  dsimp only [A] at *
  omega

/-- Quarter-cutoff switching with an explicit bad-set loss and rough P₂ output. -/
theorem chen_quarter_switching_inequality {N z y : ℕ} (hy : N<(y+1)^4) (hy3 : 3≤y) :
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      ((chenSifted N y (chenQuarterB30 N y)).card:ℝ) -
      (1/2:ℝ)*((chenSifted N y (chenQuarterB31 N z y)).card:ℝ) -
      (1/2:ℝ)*((chenSifted N y (chenQuarterB41 N z y)).card:ℝ) -
      ((chenBadSet N z y).card:ℝ) ≤ ((chenRoughRepresentations N z).card:ℝ) := by
  have h : (2:ℝ)*(chenSifted N z (chenA N)).card ≤ 2*((chenRoughRepresentations N z).card:ℝ) +
      (∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) +
      2*((chenSifted N y (chenQuarterB30 N y)).card:ℝ) +
      ((chenSifted N y (chenQuarterB31 N z y)).card:ℝ) +
      ((chenSifted N y (chenQuarterB41 N z y)).card:ℝ) + 2*((chenBadSet N z y).card:ℝ) := by
    exact_mod_cast chen_quarter_switching_twice (z:=z) hy hy3
  linarith only [h]

/-- Exact fourth-root flooring leaves enough room for the distinct-prime argument. -/
theorem chen_quarter_floor_geometry {N : ℕ} (hN : 81≤N) :
    let y := chenPowerLevel (1/4) N
    N<(y+1)^4 ∧ 3≤y := by
  let t := (N:ℝ)^(1/4:ℝ)
  have ht : 0≤t := by dsimp [t]; positivity
  have ht4 : t^4=(N:ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have ht3 : 3≤t := by
    by_contra! h
    have hlt := pow_lt_pow_left₀ h ht (by decide : 4≠0)
    have h81 : (81:ℝ)≤N := by exact_mod_cast hN
    linarith only [hlt, ht4, h81]
  have hlt := pow_lt_pow_left₀ (Nat.lt_floor_add_one t) ht (by decide : 4≠0)
  rw [ht4] at hlt
  exact ⟨by exact_mod_cast hlt, Nat.le_floor (by exact_mod_cast ht3)⟩

private theorem quarter_badSet_mono {N z₁ z₂ y₁ y₂ : ℕ} (hz : z₁≤z₂) (hy : y₁≤y₂) :
    chenBadSet N z₂ y₁ ⊆ chenBadSet N z₁ y₂ := by
  classical
  intro m hm
  obtain ⟨hs, hb⟩ := Finset.mem_filter.mp hm
  obtain ⟨hA, hr⟩ := Finset.mem_filter.mp hs
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hA, ?_⟩, ?_⟩
  · intro q hq
    exact hr q (Finset.mem_range.mpr ((Finset.mem_range.mp hq).trans_le hz))
  · rcases hb with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (h.trans_le hy)))

/-- The fourth-root upper cutoff admits the original explicit elementary error. -/
theorem chen_quarter_bad_card_le_power {N : ℕ} {α : ℝ} (hN : 2^24≤N) (hα : 1/8≤α) :
    ((chenBadSet N (chenPowerLevel α N) (chenPowerLevel (1/4) N)).card:ℝ) ≤
      2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ) := by
  have hOne : (1:ℝ)≤N := Nat.one_le_cast.mpr (by omega)
  have hz : chenLowerCutoff N≤chenPowerLevel α N :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hOne hα)
  have hy : chenPowerLevel (1/4) N≤chenUpperCutoff N :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hOne (by norm_num))
  have hb : ((chenBadSet N (chenPowerLevel α N) (chenPowerLevel (1/4) N)).card:ℝ) ≤
      chenElementaryError N := Nat.cast_le.mpr (Finset.card_le_card (quarter_badSet_mono hz hy))
  exact hb.trans (chenElementaryError_le hN)

/-- Quarter-cutoff switching at the integer floors, with the elementary error displayed. -/
theorem chen_quarter_switching_floor {N : ℕ} {α : ℝ} (hN : 2^24≤N) (hα : 1/8≤α) :
    let z := chenPowerLevel α N
    let y := chenPowerLevel (1/4) N
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      ((chenSifted N y (chenQuarterB30 N y)).card:ℝ) -
      (1/2:ℝ)*((chenSifted N y (chenQuarterB31 N z y)).card:ℝ) -
      (1/2:ℝ)*((chenSifted N y (chenQuarterB41 N z y)).card:ℝ) -
      (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) ≤ ((chenRoughRepresentations N z).card:ℝ) := by
  obtain ⟨hy,hy3⟩ := chen_quarter_floor_geometry (by omega : 81≤N)
  exact (sub_le_sub_left (chen_quarter_bad_card_le_power hN hα) _).trans
    (chen_quarter_switching_inequality hy hy3)

end FareyGoldbach
