import FareyGoldbach.ChenQuarterSwitching

open FareyGoldbach
open scoped Classical

private theorem prime_sifted_above {N y p : ℕ} (hp : p.Prime) (hpy : y ≤ p) :
    chenRough N y p := by
  intro q hq hprime _ hdiv
  have heq := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hdiv
  have hlt := Finset.mem_range.mp hq
  omega

private theorem smallCutoff_sifted {N a : ℕ} (hN : N % 2 = 0) (ha : a ≤ N)
    (hp : (N-a).Prime) : a ∈ chenSifted N 3 (chenA N) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩, ?_⟩
  intro q hq hprime hqN _
  have hlt := Finset.mem_range.mp hq
  have hge := hprime.two_le
  have heq : q = 2 := by omega
  subst q
  exact hqN (Nat.dvd_iff_mod_eq_zero.mpr hN)

private noncomputable def quarterCharge (N z y a : ℕ) : ℕ :=
  2*(if a ∈ chenRoughRepresentations N z then 1 else 0) +
    ((chenMediumPrimes z y).filter (· ∣ a)).card +
    2*(if N-a ∈ chenSifted N y (chenQuarterB30 N y) then 1 else 0) +
    (if N-a ∈ chenSifted N y (chenQuarterB31 N z y) then 1 else 0) +
    (if N-a ∈ chenSifted N y (chenQuarterB41 N z y) then 1 else 0) +
    2*(if a ∈ chenBadSet N z y then 1 else 0)

private theorem check_charge {N a : ℕ} (hcut : N < (5+1)^4) (hN : N % 2 = 0)
    (ha : a ≤ N) (hp : (N-a).Prime) : 2 ≤ quarterCharge N 3 5 a :=
  chen_quarter_two_charges hcut (by decide) (smallCutoff_sifted hN ha hp)

example : 13 ∈ chenSifted 398 5 (chenQuarterB30 398 5) ∧ 2 ≤ quarterCharge 398 3 5 385 := by
  refine ⟨Finset.mem_filter.mpr ⟨?_, prime_sifted_above (by decide) (by decide)⟩,
    check_charge (by decide) (by decide) (by decide) (by decide)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide), 5, 7, 11, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide⟩

example : 11 ∈ chenSifted 116 5 (chenQuarterB31 116 3 5) ∧ 2 ≤ quarterCharge 116 3 5 105 := by
  refine ⟨Finset.mem_filter.mpr ⟨?_, prime_sifted_above (by decide) (by decide)⟩,
    check_charge (by decide) (by decide) (by decide) (by decide)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide), 3, 5, 7, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

example : 13 ∈ chenSifted 1168 5 (chenQuarterB41 1168 3 5) ∧ 2 ≤ quarterCharge 1168 3 5 1155 := by
  refine ⟨Finset.mem_filter.mpr ⟨?_, prime_sifted_above (by decide) (by decide)⟩,
    check_charge (by decide) (by decide) (by decide) (by decide)⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by decide), 3, 5, 7, 11, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

example (N z : ℕ) : 0 ∉ chenRoughRepresentations N z := by
  intro h
  obtain ⟨_, _, _, hn, _⟩ := mem_chenRoughRepresentations_iff.mp h
  omega

example (N z : ℕ) : 1 ∉ chenRoughRepresentations N z := by
  intro h
  obtain ⟨_, _, _, hn, _⟩ := mem_chenRoughRepresentations_iff.mp h
  omega

example : 77 ∈ chenRoughRepresentations 90 7 := by
  have hp7 : Nat.Prime 7 := by decide
  have hp11 : Nat.Prime 11 := by decide
  have hsq : Squarefree (7*11 : ℕ) :=
    (Nat.squarefree_mul (by decide)).mpr ⟨hp7.prime.squarefree, hp11.prime.squarefree⟩
  refine mem_chenRoughRepresentations_iff.mpr
    ⟨13, by decide, Or.inr (Or.inr ⟨7, 11, hp7, hp11, rfl⟩), by decide, hsq, by decide, ?_, by decide⟩
  intro q hq
  change q ∈ (7*11 : ℕ).primeFactors at hq
  rw [Nat.primeFactors_mul hp7.ne_zero hp11.ne_zero, hp7.primeFactors, hp11.primeFactors] at hq
  simp only [Finset.mem_union, Finset.mem_singleton] at hq
  omega

example : 77 ∉ chenRoughRepresentations 90 8 := by
  intro h
  obtain ⟨_, _, _, _, _, _, hr, _⟩ := mem_chenRoughRepresentations_iff.mp h
  have h7 : 7 ∈ (77:ℕ).primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, by decide, by decide⟩
  have hbad := hr 7 h7
  omega
