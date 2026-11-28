import FareyGoldbach.ChenSwitching

/-! # Finite Buchstab masses under a dimension-one product bound

At a prime p the local mass is g(p) times the Euler product over smaller
primes. Its tail telescopes. Discrete summation by parts transfers an upper
bound for every tail to any nonnegative, nondecreasing test function.
-/

namespace FareyGoldbach

/-- Euler product over the members of a finite sifting set below a strict cutoff. -/
noncomputable def buchstabProduct (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) : ℝ :=
  ∏ p ∈ P.filter (· < z), (1 - g p)

/-- Local Buchstab mass, extended by zero off the sifting set. -/
noncomputable def buchstabAtom (P : Finset ℕ) (g : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p ∈ P then g p * buchstabProduct P g p else 0

theorem buchstabProduct_pos (P : Finset ℕ) {g : ℕ → ℝ} (hg : ∀ p ∈ P, g p < 1)
    (z : ℕ) : 0 < buchstabProduct P g z :=
  Finset.prod_pos fun p hp => sub_pos.mpr (hg p (Finset.mem_filter.mp hp).1)

theorem buchstabAtom_eq_sub (P : Finset ℕ) (g : ℕ → ℝ) (p : ℕ) :
    buchstabAtom P g p = buchstabProduct P g p - buchstabProduct P g (p+1) := by
  by_cases h : p ∈ P
  · have he : P.filter (· < p+1) = insert p (P.filter (· < p)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq,hle⟩
        rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hle) with he | hl
        · exact Or.inl he
        · exact Or.inr ⟨hq,hl⟩
      · rintro (rfl | ⟨hq,hl⟩)
        · exact ⟨h,Nat.lt_succ_self _⟩
        · exact ⟨hq,hl.trans (Nat.lt_succ_self _)⟩
    have hnot : p ∉ P.filter (· < p) := by simp
    simp only [buchstabAtom, ite_eq_left h, buchstabProduct, he, Finset.prod_insert hnot]
    ring
  · have he : P.filter (· < p+1) = P.filter (· < p) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq,hq'⟩
        exact ⟨hq,lt_of_le_of_ne (Nat.lt_succ_iff.mp hq') (fun he => h (he ▸ hq))⟩
      · exact fun ⟨hq,hq'⟩ => ⟨hq,hq'.trans (Nat.lt_succ_self _)⟩
    simp only [buchstabAtom, ite_eq_right h, buchstabProduct, he, sub_self]

/-- Exact unnormalized tail of the finite Buchstab measure. -/
theorem buchstab_tail_mass (P : Finset ℕ) (g : ℕ → ℝ) {w z : ℕ} (hwz : w ≤ z) :
    (∑ p ∈ Finset.Ico w z, buchstabAtom P g p) =
      buchstabProduct P g w - buchstabProduct P g z := by
  induction z, hwz using Nat.le_induction with
  | base => simp
  | succ z hz ih =>
    rw [Finset.sum_Ico_succ_top hz, ih, buchstabAtom_eq_sub]
    ring

/-- Summation by parts using upper tails. The last tail vanishes exactly. -/
theorem buchstab_weighted_tail (P : Finset ℕ) (g f : ℕ → ℝ) {w z : ℕ} (hwz : w ≤ z) :
    (∑ p ∈ Finset.Ico w z, f p * buchstabAtom P g p) =
      f w * (buchstabProduct P g w - buchstabProduct P g z) +
        ∑ p ∈ Finset.Ico w z, (f (p+1) - f p) *
          (buchstabProduct P g (p+1) - buchstabProduct P g z) := by
  induction hwz using Nat.decreasingInduction with
  | self => simp
  | of_succ w hw ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot hw, Finset.sum_eq_sum_Ico_succ_bot hw, ih,
      buchstabAtom_eq_sub]
    ring

/-- A dimension-one product bound on the tails gives an explicit weighted
discrete comparison, for an arbitrary nonnegative nondecreasing test weight. -/
theorem buchstab_weighted_dimension_one (P : Finset ℕ) (g f : ℕ → ℝ)
    {K : ℝ} {w z : ℕ} (hwz : w ≤ z) (hg : ∀ p ∈ P, g p < 1) (hfw : 0 ≤ f w)
    (hmono : MonotoneOn f (Set.Icc w z))
    (hdim : ∀ u ∈ Set.Icc w z, buchstabProduct P g u / buchstabProduct P g z ≤
      Real.log z / Real.log u * (1 + K / Real.log u)) :
    (∑ p ∈ Finset.Ico w z, f p * buchstabAtom P g p) ≤
      buchstabProduct P g z *
        (f w * (Real.log z / Real.log w * (1 + K / Real.log w) - 1) +
          ∑ p ∈ Finset.Ico w z, (f (p+1) - f p) *
            (Real.log z / Real.log (p+1 : ℕ) * (1 + K / Real.log (p+1 : ℕ)) - 1)) := by
  let B (u : ℕ) := Real.log z / Real.log u * (1 + K / Real.log u) - 1
  have hV := buchstabProduct_pos P hg z
  have htail (u : ℕ) (hu : u ∈ Set.Icc w z) :
      buchstabProduct P g u - buchstabProduct P g z ≤ B u * buchstabProduct P g z := by
    have h := (div_le_iff₀ hV).mp (hdim u hu)
    dsimp only [B]
    linarith
  rw [buchstab_weighted_tail P g f hwz, mul_comm (buchstabProduct P g z),
    add_mul, Finset.sum_mul]
  apply add_le_add
  · exact (mul_le_mul_of_nonneg_left (htail w ⟨le_rfl,hwz⟩) hfw).trans_eq (mul_assoc ..).symm
  · apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hwp,hpz⟩ := Finset.mem_Ico.mp hp
    have hps : p+1 ∈ Set.Icc w z := ⟨by omega,by omega⟩
    have hd : 0 ≤ f (p+1)-f p :=
      sub_nonneg.mpr (hmono ⟨hwp,hpz.le⟩ hps (Nat.le_succ _))
    exact (mul_le_mul_of_nonneg_left (htail (p+1) hps) hd).trans_eq (mul_assoc ..).symm

end FareyGoldbach