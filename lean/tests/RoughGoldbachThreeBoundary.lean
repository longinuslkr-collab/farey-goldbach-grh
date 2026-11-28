import FareyGoldbach

/-! Run with `lake env lean tests/RoughGoldbachThreeBoundary.lean`. -/

open FareyGoldbach

example (N z : ℕ) : 0 ∉ chenRoughThreeRepresentations N z := by
  intro hm
  obtain ⟨_, _, _, h, _⟩ := mem_chenRoughThreeRepresentations_iff.mp hm
  omega

example (N z : ℕ) : 1 ∉ chenRoughThreeRepresentations N z := by
  intro hm
  obtain ⟨_, _, _, h, _⟩ := mem_chenRoughThreeRepresentations_iff.mp hm
  omega

example : ¬ IsAlmostPrimeThree (2 * 3 * 5 * 7) := by
  have hlist : List.Perm (210 : ℕ).primeFactorsList [2, 3, 5, 7] := by
    symm
    apply Nat.primeFactorsList_unique (by decide)
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  change ¬ (0 < 210 ∧ (210 : ℕ).primeFactorsList.length ≤ 3)
  simpa only [hlist.length_eq] using
    (by decide : ¬ ((0:ℕ) < 210 ∧ ([2, 3, 5, 7] : List ℕ).length ≤ 3))

example : 105 ∈ chenRoughThreeRepresentations 116 3 := by
  have hlist : List.Perm (105 : ℕ).primeFactorsList [3, 5, 7] := by
    symm
    apply Nat.primeFactorsList_unique (by decide)
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  have hlen : (105 : ℕ).primeFactorsList.length ≤ 3 := by
    simpa only [hlist.length_eq] using (by decide : ([3, 5, 7] : List ℕ).length ≤ 3)
  apply mem_chenRoughThreeRepresentations_iff.mpr
  refine ⟨11, by decide, ⟨by decide, hlen⟩, by decide, ?_, by decide, ?_, by decide⟩
  · apply (Nat.squarefree_iff_nodup_primeFactorsList (by decide)).2
    exact hlist.nodup_iff.mpr (by decide)
  · intro q hq
    have hq' := hlist.mem_iff.mp (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hq)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
    omega
