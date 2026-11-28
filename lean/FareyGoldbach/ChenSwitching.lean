import FareyGoldbach.ChenPrimeFactors
import FareyGoldbach.RoughGoldbachDefinitions

/-! # Chen's finite switching inequality

The first sieve uses all prime complements, and its sifting primes omit divisors of
`N`. The switched carrier includes the coprimality condition on the triple product.
The elementary loss is displayed as a finite set. -/

namespace FareyGoldbach

open scoped Classical

/-- Prime complements in the closed interval from zero to `N`. -/
def chenA (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter (fun a ↦ (N-a).Prime)

def chenDivisible (A : Finset ℕ) (q : ℕ) : Finset ℕ := A.filter (q ∣ ·)

def chenMediumPrimes (z y : ℕ) : Finset ℕ := (Finset.Ico z y).filter Nat.Prime

def chenRough (N z a : ℕ) : Prop :=
  ∀ q ∈ Finset.range z, q.Prime → ¬q ∣ N → ¬q ∣ a

noncomputable def chenSifted (N z : ℕ) (A : Finset ℕ) : Finset ℕ := A.filter (chenRough N z)

/-- Ordered prime triples are switched back to their complements. -/
noncomputable def chenB (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun b ↦ ∃ u v w : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧ z≤u ∧ u<y ∧ y≤v ∧ v≤w ∧
      u*v*w<N ∧ (u*v*w).Coprime N ∧ b=N-u*v*w

/-- The switched carrier allowing every triple, including products sharing a factor with `N`. -/
noncomputable def chenUnrestrictedB (N z y : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun b ↦ ∃ u v w : ℕ,
    u.Prime ∧ v.Prime ∧ w.Prime ∧ z≤u ∧ u<y ∧ y≤v ∧ v≤w ∧
      u*v*w<N ∧ b=N-u*v*w

theorem chenB_subset_unrestricted (N z y : ℕ) : chenB N z y ⊆ chenUnrestrictedB N z y := by
  intro b hb
  obtain ⟨hN,u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,hlt,_,heq⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hN,u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,hlt,heq⟩

/-- Every prime-or-semiprime complement, including one under the empty-product convention. -/
noncomputable def chenCount (N : ℕ) : ℕ := ((chenA N).filter IsAlmostPrimeTwo).card

/-- Prime summands whose complement is a product of at most two primes. -/
noncomputable def chenRepresentations (N : ℕ) : Finset ℕ :=
  (Finset.range (N+1)).filter fun p ↦ p.Prime ∧ IsAlmostPrimeTwo (N-p)

/-- Counting prime complements agrees with counting the prime summands. -/
theorem chenCount_eq_prime_count (N : ℕ) : chenCount N =
    ((Finset.range (N+1)).filter fun p ↦ p.Prime ∧ IsAlmostPrimeTwo (N-p)).card := by
  classical
  unfold chenCount
  apply Finset.card_bij' (fun a _ ↦ N-a) (fun p _ ↦ N-p)
  · intro a ha
    obtain ⟨hA,ha₂⟩ := Finset.mem_filter.mp ha
    obtain ⟨hab,hp⟩ := Finset.mem_filter.mp hA
    have hle := Finset.mem_range.mp hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp,by rwa [show N-(N-a)=a by omega]⟩
  · intro p hp
    obtain ⟨hpr,hp₁,hp₂⟩ := Finset.mem_filter.mp hp
    have hle := Finset.mem_range.mp hpr
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega),by rwa [show N-(N-p)=p by omega]⟩,hp₂⟩
  · intro a ha
    have hle := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    omega

  · intro p hp
    have hle := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega

theorem chenCount_eq_representations_card (N : ℕ) : chenCount N=(chenRepresentations N).card :=
  chenCount_eq_prime_count N

/-- Exceptional complements removed from the pointwise switching argument. -/
noncomputable def chenBadSet (N z y : ℕ) : Finset ℕ :=
  (chenSifted N z (chenA N)).filter
    fun a ↦ a<2 ∨ ¬a.Coprime N ∨ ¬Squarefree a ∨ N-a<y

theorem chenRough_primeFactors {N z a : ℕ} (hr : chenRough N z a) (hcop : a.Coprime N) :
    ∀ q ∈ a.primeFactors, z≤q := by
  intro q hq
  have hp := Nat.prime_of_mem_primeFactors hq
  have hd := Nat.dvd_of_mem_primeFactors hq
  by_contra! h
  exact hr q (Finset.mem_range.mpr h) hp
    (fun hqN ↦ Nat.not_coprime_of_dvd_of_dvd hp.one_lt hd hqN hcop) hd

/-- Rough, squarefree Chen representations indexed by their complement `m`.
The prime summand is uniquely determined as `N - m`. -/
noncomputable def chenRoughRepresentations (N z : ℕ) : Finset ℕ :=
  (chenA N).filter fun m ↦ IsAlmostPrimeTwo m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧ IsRough z m

theorem mem_chenRoughRepresentations_iff {N z m : ℕ} :
    m ∈ chenRoughRepresentations N z ↔
      ∃ p : ℕ, p.Prime ∧ IsAlmostPrimeTwo m ∧ 1 < m ∧ Squarefree m ∧ m.Coprime N ∧
        IsRough z m ∧ p + m = N := by
  classical
  constructor
  · intro hm
    obtain ⟨hA, hP, hm₁, hsq, hcop, hr⟩ := Finset.mem_filter.mp hm
    obtain ⟨hbound, hprime⟩ := Finset.mem_filter.mp hA
    have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hbound)
    exact ⟨N - m, hprime, hP, hm₁, hsq, hcop, hr, Nat.sub_add_cancel hmN⟩
  · rintro ⟨p, hp, hP, hm₁, hsq, hcop, hr, heq⟩
    have hA : m ∈ chenA N :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by rwa [show N - m = p by omega]⟩
    exact Finset.mem_filter.mpr ⟨hA, hP, hm₁, hsq, hcop, hr⟩

theorem chenRoughRepresentations_card_le_chenCount (N z : ℕ) :
    (chenRoughRepresentations N z).card ≤ chenCount N := by
  classical
  apply Finset.card_le_card
  intro m hm
  obtain ⟨hA, hP, _⟩ := Finset.mem_filter.mp hm
  exact Finset.mem_filter.mpr ⟨hA, hP⟩

theorem chen_sifted_incident_sum (N z y : ℕ) (A : Finset ℕ) :
    (∑ a ∈ chenSifted N z A, ((chenMediumPrimes z y).filter (· ∣ a)).card) =
      ∑ q ∈ chenMediumPrimes z y, (chenSifted N z (chenDivisible A q)).card := by
  classical
  calc
    _ = ∑ a ∈ chenSifted N z A, ∑ q ∈ chenMediumPrimes z y,
          if q ∣ a then (1:ℕ) else 0 := by simp
    _ = ∑ q ∈ chenMediumPrimes z y, ∑ a ∈ chenSifted N z A,
          if q ∣ a then (1:ℕ) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext a
      simp only [chenSifted, chenDivisible, Finset.mem_filter]
      tauto

private theorem reflected_card (N z y : ℕ) :
    ((chenSifted N z (chenA N)).filter
      (fun a ↦ N-a ∈ chenSifted N y (chenB N z y))).card ≤
        (chenSifted N y (chenB N z y)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun a ↦ N-a) (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  intro a ha b hb h
  have ha' := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1).1
  have hb' := Finset.mem_range.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1).1
  change N-a=N-b at h
  omega

private theorem mem_switched_sift {N z y a u v w : ℕ} (haN : a≤N) (hp : (N-a).Prime)
    (hpy : y≤N-a) (hcop : a.Coprime N) (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (hzu : z≤u) (huy : u<y) (hyv : y≤v) (hvw : v≤w) (heq : a=u*v*w) :
    N-a ∈ chenSifted N y (chenB N z y) := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_filter.mpr
    have hp0 := hp.pos
    exact ⟨Finset.mem_range.mpr (by omega),u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,
      by omega, heq ▸ hcop, by rw [heq]⟩
  · intro q hq hqp _ hd
    have he := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hd
    have hq' := Finset.mem_range.mp hq
    omega

private theorem two_charges_rough {N z y a : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y)
    (ha : a ∈ chenSifted N z (chenA N)) :
    2 ≤ 2*(if a ∈ chenRoughRepresentations N z then 1 else 0) +
      ((chenMediumPrimes z y).filter (· ∣ a)).card +
      (if N-a ∈ chenSifted N y (chenB N z y) then 1 else 0) +
      2*(if a ∈ chenBadSet N z y then 1 else 0) := by
  classical
  by_cases hb : a ∈ chenBadSet N z y
  · simp only [ite_eq_left hb]; omega
  have hn : ¬(a<2 ∨ ¬a.Coprime N ∨ ¬Squarefree a ∨ N-a<y) :=
    fun h ↦ hb (Finset.mem_filter.mpr ⟨ha,h⟩)
  push Not at hn
  obtain ⟨ha2,hcop,hsq,hpy⟩ := hn
  obtain ⟨hA,hrough⟩ := Finset.mem_filter.mp ha
  obtain ⟨hN,hp⟩ := Finset.mem_filter.mp hA
  have haN : a≤N := by simpa using Finset.mem_range.mp hN
  have hrf := chenRough_primeFactors hrough hcop
  by_cases hg : IsAlmostPrimeTwo a
  · have hgood : a ∈ chenRoughRepresentations N z :=
      Finset.mem_filter.mpr ⟨hA, hg, by omega, hsq, hcop, hrf⟩
    simp only [ite_eq_left hgood]
    omega
  have hmed {q : ℕ} (hq : q∈a.primeFactors) (hs : q<y) :
      q∈(chenMediumPrimes z y).filter (· ∣ a) :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hrf q hq,hs⟩,Nat.prime_of_mem_primeFactors hq⟩,
      Nat.dvd_of_mem_primeFactors hq⟩
  rcases chen_squarefree_dichotomy hy hy3 ha2 haN hsq hrf with h | h | h
  · exact (hg ((isAlmostPrimeTwo_iff_primeFactorsList_length_le_two (by omega)).2 h)).elim
  · obtain ⟨q,hq,s,hs,hne,hqy,hsy⟩ := h
    have htwo : 2 ≤ ((chenMediumPrimes z y).filter (· ∣ a)).card :=
      Finset.Nontrivial.two_le_card ⟨q,hmed hq hqy,s,hmed hs hsy,hne⟩
    omega
  · obtain ⟨u,v,w,hu,hv,hw,hzu,huy,hyv,hvw,heq⟩ := h
    have huD : u∣a := ⟨v*w, by rw [heq]; ac_rfl⟩
    have hm := hmed (Nat.mem_primeFactors.mpr ⟨hu,huD,by omega⟩) huy
    have hc := Finset.card_pos.mpr ⟨u,hm⟩
    have hsw := mem_switched_sift haN hp hpy hcop hu hv hw hzu huy hyv hvw heq
    simp only [ite_eq_left hsw]; omega

theorem two_charges {N z y a : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y)
    (ha : a ∈ chenSifted N z (chenA N)) :
    2 ≤ 2*(if IsAlmostPrimeTwo a then 1 else 0) +
      ((chenMediumPrimes z y).filter (· ∣ a)).card +
      (if N-a ∈ chenSifted N y (chenB N z y) then 1 else 0) +
      2*(if a ∈ chenBadSet N z y then 1 else 0) := by
  classical
  by_cases hg : IsAlmostPrimeTwo a
  · simp only [ite_eq_left hg]
    omega
  · have hgood : a ∉ chenRoughRepresentations N z := fun hm ↦ hg (Finset.mem_filter.mp hm).2.1
    simpa only [hg, hgood, ite_false] using two_charges_rough hy hy3 ha

private theorem chen_switching_twice_rough {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    2*(chenSifted N z (chenA N)).card ≤ 2*(chenRoughRepresentations N z).card +
      (∑ q ∈ chenMediumPrimes z y, (chenSifted N z (chenDivisible (chenA N) q)).card) +
      (chenSifted N y (chenB N z y)).card + 2*(chenBadSet N z y).card := by
  classical
  let A := chenSifted N z (chenA N)
  let B := chenSifted N y (chenB N z y)
  have hs := Finset.sum_le_sum (s:=A) (fun a ha ↦ two_charges_rough hy hy3 ha)
  simp only [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Nat.cast_id] at hs
  have hGood : (A.filter (· ∈ chenRoughRepresentations N z)).card ≤ (chenRoughRepresentations N z).card :=
    Finset.card_le_card (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  have hBad : (A.filter (·∈chenBadSet N z y)).card ≤ (chenBadSet N z y).card :=
    Finset.card_le_card (fun _ ha ↦ (Finset.mem_filter.mp ha).2)
  have hRef := reflected_card N z y
  have hInc := chen_sifted_incident_sum N z y (chenA N)
  dsimp only [A,B] at *
  omega

/-- The pointwise charges summed over the sifted complements, before division by two. -/
theorem chen_switching_twice {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    2*(chenSifted N z (chenA N)).card ≤ 2*chenCount N +
      (∑ q ∈ chenMediumPrimes z y, (chenSifted N z (chenDivisible (chenA N) q)).card) +
      (chenSifted N y (chenB N z y)).card + 2*(chenBadSet N z y).card := by
  have hs := chen_switching_twice_rough (z:=z) hy hy3
  have hc := chenRoughRepresentations_card_le_chenCount N z
  omega

private theorem chen_switching_inequality_rough {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenB N z y)).card:ℝ) - ((chenBadSet N z y).card:ℝ) ≤
        ((chenRoughRepresentations N z).card:ℝ) := by
  have h := chen_switching_twice_rough (z:=z) hy hy3
  have h' : (2:ℝ)*(chenSifted N z (chenA N)).card ≤ 2*((chenRoughRepresentations N z).card:ℝ) +
      (∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) +
      (chenSifted N y (chenB N z y)).card + 2*((chenBadSet N z y).card:ℝ) := by exact_mod_cast h
  linarith

/-- Chen's switching inequality with an explicit finite elementary loss. -/
theorem chen_switching_inequality {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenB N z y)).card:ℝ) - ((chenBadSet N z y).card:ℝ) ≤
        (chenCount N:ℝ) := by
  exact (chen_switching_inequality_rough hy hy3).trans
    (Nat.cast_le.mpr (chenRoughRepresentations_card_le_chenCount N z))

/-- Chen's switching inequality for rough representations on the unrestricted switched carrier. -/
theorem chen_switching_inequality_rough_unrestricted {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenUnrestrictedB N z y)).card:ℝ) - ((chenBadSet N z y).card:ℝ) ≤
        ((chenRoughRepresentations N z).card:ℝ) := by
  have hs : chenSifted N y (chenB N z y) ⊆ chenSifted N y (chenUnrestrictedB N z y) := by
    intro b hb
    obtain ⟨hB,hb⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_filter.mpr ⟨chenB_subset_unrestricted N z y hB,hb⟩
  have hc : ((chenSifted N y (chenB N z y)).card:ℝ) ≤ (chenSifted N y (chenUnrestrictedB N z y)).card :=
    Nat.cast_le.mpr (Finset.card_le_card hs)
  linarith only [hc,chen_switching_inequality_rough (z:=z) hy hy3]

/-- The same inequality on the unrestricted, hence larger, switched carrier. -/
theorem chen_switching_inequality_unrestricted {N z y : ℕ} (hy : N<(y+1)^3) (hy3 : 3≤y) :
    ((chenSifted N z (chenA N)).card:ℝ) -
      (1/2:ℝ)*(∑ q ∈ chenMediumPrimes z y, ((chenSifted N z (chenDivisible (chenA N) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted N y (chenUnrestrictedB N z y)).card:ℝ) - ((chenBadSet N z y).card:ℝ) ≤
        (chenCount N:ℝ) := by
  exact (chen_switching_inequality_rough_unrestricted hy hy3).trans
    (Nat.cast_le.mpr (chenRoughRepresentations_card_le_chenCount N z))

end FareyGoldbach
