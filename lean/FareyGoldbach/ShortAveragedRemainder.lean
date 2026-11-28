import FareyGoldbach.AveragedRemainder
import FareyGoldbach.LocalTwistedMeanSquare

/-! # Continuous local principal terms and class averages -/

open Real Complex Set MeasureTheory
open scoped BigOperators Classical

namespace FareyGoldbach

/-- The centered prime sum on one unit fiber, with the continuous principal term. -/
noncomputable def shortUnitDiscrepancy (r q Y : ℕ) [NeZero (r * q)] (β : ℝ) (u : ZMod (r * q)) : ℂ :=
  (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        e ((β / (r : ℝ)) * (n : ℝ))) -
    ((1 : ℂ) / ((r * q).totient : ℂ)) *
      shortContinuousMain Y (β / (r : ℝ))

theorem shortUnitDiscrepancy_character {r q Y : ℕ} (hr : 0 < r) (hq : 0 < q)
    [NeZero (r * q)] (χ : DirichletCharacter ℂ (r * q)) (β : ℝ) :
    (∑ u ∈ zmodUnitsFinset (r * q), shortUnitDiscrepancy r q Y β u * χ u) =
      shortPrimeTwistedRemainder χ Y (β / (r : ℝ)) := by
  have hrq_pos := Nat.mul_pos hr hq
  let U_sum := shortContinuousMain Y (β / (r : ℝ))
  unfold shortUnitDiscrepancy
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hfirst : ∑ u ∈ zmodUnitsFinset (r * q),
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            e ((β / (r : ℝ)) * (n : ℝ))) * χ u =
      ∑ n ∈ Finset.Icc 1 Y,
        (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
          χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
    have hstep1 : ∀ u ∈ zmodUnitsFinset (r * q),
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            e ((β / (r : ℝ)) * (n : ℝ))) * χ u =
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
          (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
            χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      intro u _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(Finset.mem_filter.mp hn).2]; ring
    rw [Finset.sum_congr rfl hstep1]
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.Icc 1 Y).filter (fun n : ℕ => IsUnit (n : ZMod (r * q))))
      (t := zmodUnitsFinset (r * q))
      (g := fun n : ℕ => (n : ZMod (r * q)))
      (fun n hn => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hn).2⟩)
      (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)))
    have hcong : ∑ u ∈ zmodUnitsFinset (r * q),
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) =
        ∑ u ∈ zmodUnitsFinset (r * q),
          ∑ n ∈ ((Finset.Icc 1 Y).filter (fun n : ℕ => IsUnit (n : ZMod (r * q)))).filter
              (fun n : ℕ => (n : ZMod (r * q)) = u),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      refine Finset.sum_congr rfl fun u hu => Finset.sum_congr ?_ fun _ _ => rfl
      ext n; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hn1, hn2⟩; exact ⟨⟨hn1, hn2.symm ▸ (Finset.mem_filter.mp hu).2⟩, hn2⟩
      · rintro ⟨⟨hn1, _⟩, hn2⟩; exact ⟨hn1, hn2⟩
    rw [hcong, hfib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hu : IsUnit (n : ZMod (r * q))
    · simp [hu]
    · rw [ite_eq_right hu, MulChar.map_nonunit χ hu]; ring
  have hsecond : ∑ u ∈ zmodUnitsFinset (r * q),
        ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u =
      (if χ = 1 then (1 : ℂ) else 0) * U_sum := by
    have hpull : ∑ u ∈ zmodUnitsFinset (r * q),
          ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u =
        ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * ∑ u ∈ zmodUnitsFinset (r * q), χ u := by
      exact (Finset.mul_sum _ _ _).symm
    rw [hpull, sum_dirichletChar_over_units]
    have hφC : ((r * q).totient : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hrq_pos).ne'
    split_ifs
    · field_simp [hφC]
    · ring
  rw [hfirst]
  change (∑ n ∈ Finset.Icc 1 Y,
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        χ (n : ZMod (r * q)) * e ((β / (r : ℝ)) * (n : ℝ))) -
    ∑ u ∈ zmodUnitsFinset (r * q),
      ((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum * χ u = _
  rw [hsecond]
  unfold shortPrimeTwistedRemainder shortTwistedRemainderWith
  congr 1
  · refine Finset.sum_congr rfl fun n _ => ?_
    unfold scaledTiltedBump
    ring
  · dsimp [U_sum]
    split_ifs <;> ring

/-- The exact principal term in one rational cell, before selecting a Voronoi center. -/
noncomputable def shortLocalMain (r b Y a q : ℕ) [NeZero (r * q)] (β : ℝ) : ℂ :=
  (e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
    charCoeff r q a b (1 : DirichletCharacter ℂ (r * q))) *
    (e (-((β * (b : ℝ)) / (r : ℝ))) * shortContinuousMain Y (β / (r : ℝ)))

noncomputable def shortLocalRemainder (r b Y a q : ℕ) [NeZero (r * q)] (β : ℝ) : ℂ :=
  smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) - shortLocalMain r b Y a q β

/-- The principal term cancels exactly. The only correction to the
fiber discrepancy comes from primes dividing `q`. -/
theorem shortLocalRemainder_le {r q a b Y : ℕ}
    (hr : 0 < r) (hq : 0 < q) (hqY : q ≤ Y) (hY : 2 ≤ Y)
    (hb : b < r) (hbr : Nat.Coprime b r) [NeZero (r * q)] (β : ℝ) :
    ‖shortLocalRemainder r b Y a q β‖ ≤
      ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          shortUnitDiscrepancy r q Y β u‖ + Real.log (2 * (Y : ℝ)) := by
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  let U_sum := shortContinuousMain Y (β / (r : ℝ))
  let F_sum : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
      shortUnitDiscrepancy r q Y β u
  let NC_sum : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
      (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
        e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))
  let M_main : ℂ := e (-((β * (b : ℝ)) / (r : ℝ))) *
    (((1 : ℂ) / ((r * q).totient : ℂ)) * U_sum *
      ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)))
  -- Step 1: Exact identity `smoothedPrimeSum r b Y (a / q + β) = F_sum + NC_sum + M_main`.
  have hS_eq : smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) = F_sum + NC_sum + M_main := by
    -- Reindex `smoothedPrimeSum` to `n ∈ (Icc 1 Y).filter (fun n => n % r = b)`.
    have hreidx : smoothedPrimeSum r b Y ((a : ℝ) / (q : ℝ) + β) =
        e (-((β * (b : ℝ)) / (r : ℝ))) *
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) := by
      unfold smoothedPrimeSum
      rw [Finset.mul_sum]
      let J0 := (Finset.range (Y / r + 1)).filter (fun j => 1 ≤ r * j + b ∧ r * j + b ≤ Y)
      have htrim : ∑ j ∈ Finset.range (Y / r + 1),
            ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) *
              e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) =
          ∑ j ∈ J0,
            ((quarticBump ((r * j + b : ℝ) / (Y : ℝ)) * primeWeight (r * j + b) : ℝ) : ℂ) *
              e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) := by
        symm; rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h
        · rfl
        · have hw0 : quarticBump ((r * j + b : ℝ) / (Y : ℝ)) = 0 := by
            unfold quarticBump
            have hnot : ¬ (0 < (r * j + b : ℝ) / (Y : ℝ) ∧ (r * j + b : ℝ) / (Y : ℝ) < 1) := by
              rintro ⟨h1, h2⟩
              have hcast : ((r * j + b : ℕ) : ℝ) = (r * j + b : ℝ) := by push_cast; rfl
              have h1' : (0 : ℕ) < r * j + b := by
                have := (div_pos_iff_of_pos_right hY_pos).1 h1; rw [← hcast] at this; exact_mod_cast this
              have h2' : r * j + b < Y := by
                have := (div_lt_one hY_pos).1 h2; rw [← hcast] at this; exact_mod_cast this
              exact h ⟨by omega, by omega⟩
            simp [hnot]
          simp [hw0]
      rw [htrim]
      refine Finset.sum_bij (fun j _ => r * j + b) ?_ ?_ ?_ ?_
      · intro j hj
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (Finset.mem_filter.mp hj).2, ?_⟩
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      · intro j₁ _ j₂ _ hEq; exact Nat.eq_of_mul_eq_mul_left hr (by omega)
      · intro n hn
        have hIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
        have hmod := (Finset.mem_filter.mp hn).2
        have hnj : r * (n / r) + b = n := by have := Nat.div_add_mod n r; omega
        refine ⟨n / r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.div_le_div_right hIcc.2)), hnj.symm ▸ hIcc.1, hnj.symm ▸ hIcc.2⟩, hnj⟩
      · intro j _
        have hsub_div : (r * j + b - b) / r = j := by rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hr]
        rw [hsub_div]
        have hexp : e (((a : ℝ) / (q : ℝ) + β) * (j : ℝ)) =
            e (-((β * (b : ℝ)) / (r : ℝ))) *
              (e ((a : ℝ) * (j : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * ((r * j + b : ℕ) : ℝ))) := by
          rw [← e_add, ← e_add]; congr 1; push_cast; field_simp [hr_pos.ne', hq_pos.ne']; ring
        rw [hexp]; push_cast; ring
    rw [hreidx]
    -- Split `n` into `Nat.Coprime n (r * q)` and `¬ Nat.Coprime n (r * q)`.
    have hsplit_cop :
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) =
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))) +
        (∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))) := by
      have h := (Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 Y).filter (fun n => n % r = b)) (fun n => Nat.Coprime n (r * q))
        (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
          e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))).symm
      have hf1 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)) := by ext n; simp [and_assoc]
      have hf2 : ((Finset.Icc 1 Y).filter (fun n => n % r = b)).filter (fun n => ¬ Nat.Coprime n (r * q)) =
          (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q)) := by ext n; simp [and_assoc]
      rwa [hf1, hf2] at h
    -- Partition the coprime sum by `u = (n : ZMod (r * q)) ∈ charSupp r q b`.
    have hcop_fiber :
        ∑ n ∈ (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)) =
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
          ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((β / (r : ℝ)) * (n : ℝ)) := by
      have hfib := (Finset.sum_fiberwise_of_maps_to
        (s := (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q)))
        (t := charSupp r q b)
        (g := fun n : ℕ => (n : ZMod (r * q)))
        (fun n hn => by
          have h2 := (Finset.mem_filter.mp hn).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ZMod.isUnit_iff_coprime n (r * q)).2 h2.2, ?_⟩
          rw [ZMod.val_natCast, Nat.mod_mul_right_mod, h2.1, Nat.mod_eq_of_lt hb])
        (fun n => (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
          e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ)))).symm
      rw [hfib]
      refine Finset.sum_congr rfl fun u hu => ?_
      have hset : ((Finset.Icc 1 Y).filter (fun n => n % r = b ∧ Nat.Coprime n (r * q))).filter
            (fun n : ℕ => (n : ZMod (r * q)) = u) =
          (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u) := by
        ext n; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hn1, _⟩, hn2⟩; exact ⟨hn1, hn2⟩
        · rintro ⟨hn1, hn2⟩
          have hu' := (Finset.mem_filter.mp hu).2
          have hmod : n % r = b := by
            have h1 := congrArg ZMod.val hn2
            rw [ZMod.val_natCast] at h1
            have h2 : n % r = u.val % r := by rw [← h1, Nat.mod_mul_right_mod]
            rw [h2, hu'.2, Nat.mod_eq_of_lt hb]
          have hcop : Nat.Coprime n (r * q) := (ZMod.isUnit_iff_coprime n (r * q)).1 (hn2.symm ▸ hu'.1)
          exact ⟨⟨hn1, hmod, hcop⟩, hn2⟩
      rw [hset, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hnu : (n : ZMod (r * q)) = u := (Finset.mem_filter.mp hn).2
      have hmod_rq : n % (r * q) = u.val := by
        have := congrArg ZMod.val hnu; rwa [ZMod.val_natCast] at this
      have hmod_r : n % r = b := by
        have h1 : n % r = u.val % r := by rw [← hmod_rq, Nat.mod_mul_right_mod]
        rw [h1, (Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
      -- Show `(n - b) / r ≡ u.val / r [MOD q]`.
      have he_eq : e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) =
          e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) := by
        have hnb : (n - b) / r = n / r := by
          conv_lhs => rw [← Nat.div_add_mod n r, hmod_r]
          rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hr]
        have hdiv_n : r * ((n - b) / r) + b = n := by
          rw [hnb, ← hmod_r]; exact Nat.div_add_mod n r
        have hdiv_u : r * (u.val / r) + b = u.val := by
          have hd := Nat.div_add_mod u.val r
          have hmu : u.val % r = b := by rw [(Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
          omega
        let t := n / (r * q)
        have hdiv_rq : r * q * t + u.val = n := by
          dsimp [t]; rw [← hmod_rq]; exact Nat.div_add_mod n (r * q)
        have hq_diff : (n - b) / r = q * t + u.val / r := by
          apply Nat.eq_of_mul_eq_mul_left hr
          nlinarith
        apply e_eq_of_sub_int (k := ((a * t : ℕ) : ℤ))
        have hcast : (((n - b) / r : ℕ) : ℝ) = (q : ℝ) * (t : ℝ) + ((u.val / r : ℕ) : ℝ) := by
          exact_mod_cast hq_diff
        rw [hcast, Int.cast_natCast, Nat.cast_mul]; field_simp [hq_pos.ne']; ring
      rw [he_eq]; ring
    rw [hsplit_cop, hcop_fiber, mul_add]
    have hsplit_u :
        e (-((β * (b : ℝ)) / (r : ℝ))) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n : ℕ => (n : ZMod (r * q)) = u),
              (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
                e ((β / (r : ℝ)) * (n : ℝ)) = F_sum + M_main := by
      dsimp only [F_sum, M_main]
      rw [← mul_add]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [shortUnitDiscrepancy, U_sum]
      ring
    rw [hsplit_u]; ring
  -- Step 2: Bound `‖NC_sum‖ ≤ log(2 * Y)`.
  have hNC_le : ‖NC_sum‖ ≤ Real.log (2 * (Y : ℝ)) := by
    dsimp [NC_sum]
    rw [norm_mul, norm_e, one_mul]
    let Snc := (Finset.Icc 1 Y).filter (fun n => n % r = b ∧ ¬ Nat.Coprime n (r * q))
    have hsub_pf : Snc.filter Nat.Prime ⊆ q.primeFactors := by
      intro p hp
      have hmem := Finset.mem_filter.mp hp
      have hpr : p.Prime := hmem.2
      have h1 := (Finset.mem_filter.mp hmem.1).2
      have hcop_r : Nat.Coprime p r := by
        rw [Nat.Coprime, Nat.ModEq.gcd_eq (show p ≡ b [MOD r] by rw [Nat.ModEq, h1.1, Nat.mod_eq_of_lt hb])]
        exact hbr.gcd_eq_one
      have hncop_q : ¬ Nat.Coprime p q := fun hcq => h1.2 (hcop_r.mul_right hcq)
      have hpdvd : p ∣ q := by
        by_contra hnd; exact hncop_q (hpr.coprime_iff_not_dvd.2 hnd)
      exact Nat.mem_primeFactors.mpr ⟨hpr, hpdvd, hq.ne'⟩
    calc ‖∑ n ∈ Snc,
            (quarticBump ((n : ℝ) / (Y : ℝ)) : ℂ) * ((primeWeight n : ℝ) : ℂ) *
              e ((a : ℝ) * (((n - b) / r : ℕ) : ℝ) / (q : ℝ)) * e ((β / (r : ℝ)) * (n : ℝ))‖
        ≤ ∑ n ∈ Snc, primeWeight n := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
          rw [norm_mul, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (quarticBump_nonneg _), abs_of_nonneg (primeWeight_nonneg _)]
          exact mul_le_of_le_one_left (primeWeight_nonneg _) (quarticBump_le_one _)
      _ = ∑ p ∈ Snc.filter Nat.Prime, Real.log (p : ℝ) := by
          symm
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          unfold primeWeight; split_ifs <;> rfl
      _ ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_pf fun p hp _ =>
            Real.log_nonneg (Nat.one_le_cast.mpr (Nat.prime_of_mem_primeFactors hp).pos)
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) :=
          (Real.log_prod fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne').symm
      _ ≤ Real.log (q : ℝ) := by
          apply Real.log_le_log (Finset.prod_pos fun p hp => Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos)
          rw [← Nat.cast_prod]
          exact Nat.cast_le.mpr (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
      _ ≤ Real.log (2 * (Y : ℝ)) := Real.log_le_log hq_pos (by
          have : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY; linarith)
  have hcc_eq : ((1 : ℂ) / ((r * q).totient : ℂ)) *
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) =
      e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
        charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) := by
    unfold charCoeff
    have h1 : charCoeff r q a b (1 : DirichletCharacter ℂ (r * q)) =
        ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ)) := by
      unfold charCoeff charSupp
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      rw [MulChar.one_apply (Finset.mem_filter.mp hu).2.1, star_one, mul_one]
    change ((1 : ℂ) / ((r * q).totient : ℂ)) *
        ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) = _
    have h2 : e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
          (((1 : ℂ) / ((r * q).totient : ℂ)) *
            ∑ u ∈ charSupp r q b, e ((a : ℝ) * (u.val : ℝ) / ((r * q : ℕ) : ℝ))) =
        ((1 : ℂ) / ((r * q).totient : ℂ)) *
          ∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) := by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun u hu => ?_
      have hmu : u.val % r = b := by rw [(Finset.mem_filter.mp hu).2.2, Nat.mod_eq_of_lt hb]
      have hdiv : r * (u.val / r) + b = u.val := by have := Nat.div_add_mod u.val r; omega
      rw [← e_add]; congr 1
      have hdivR : (r : ℝ) * ((u.val / r : ℕ) : ℝ) + (b : ℝ) = (u.val : ℝ) := by exact_mod_cast hdiv
      push_cast; field_simp [hr_pos.ne', hq_pos.ne']; nlinarith
    exact h2.symm.trans (by
      unfold charSupp
      congr 2; refine Finset.sum_congr rfl fun u hu => ?_
      rw [MulChar.one_apply (Finset.mem_filter.mp hu).2.1, star_one, mul_one])
  have hM_rew : M_main =
      (e (-((a : ℝ) * (b : ℝ) / ((r * q : ℕ) : ℝ))) *
        charCoeff r q a b (1 : DirichletCharacter ℂ (r * q))) *
      (e (-((β * (b : ℝ)) / (r : ℝ))) * U_sum) := by
    dsimp [M_main]
    rw [← hcc_eq]; ring
  have hM : M_main = shortLocalMain r b Y a q β := hM_rew
  unfold shortLocalRemainder
  rw [hS_eq, ← hM, add_sub_cancel_right]
  have hF_norm : ‖F_sum‖ =
      ‖∑ u ∈ charSupp r q b, e ((a : ℝ) * ((u.val / r : ℕ) : ℝ) / (q : ℝ)) *
        shortUnitDiscrepancy r q Y β u‖ := by
    dsimp [F_sum]; rw [norm_mul, norm_e, one_mul]
  exact (norm_add_le _ _).trans (add_le_add (le_of_eq hF_norm) hNC_le)

theorem continuous_shortUnitDiscrepancy (r q Y : ℕ) [NeZero (r * q)] (u : ZMod (r*q)) :
    Continuous (fun β => shortUnitDiscrepancy r q Y β u) := by
  unfold shortUnitDiscrepancy
  refine (continuous_sum_finset _ fun n _ => continuous_const.mul ?_).sub
    (continuous_const.mul ((continuous_shortContinuousMain Y).comp (continuous_id.div_const _)))
  exact continuous_e_real.comp ((continuous_id.div_const _).mul_const _)

theorem continuous_shortLocalRemainder (r b Y a q : ℕ) [NeZero (r * q)] :
    Continuous (shortLocalRemainder r b Y a q) := by
  unfold shortLocalRemainder shortLocalMain
  refine ((continuous_smoothedPrimeSum r b Y).comp (continuous_const.add continuous_id)).sub ?_
  exact continuous_const.mul ((continuous_e_real.comp
    (((continuous_id.mul_const _).div_const _).neg)).mul
    ((continuous_shortContinuousMain Y).comp (continuous_id.div_const _)))

private lemma short_log_modulus_bound {r q Y : ℕ} (hr : 0 < r) (hq : 0 < q)
    (hrY : r ≤ Y) (hqY : q ≤ Y) (hY : 2 ≤ Y) :
    Real.log (2 * ((r*q : ℕ) : ℝ) * (Y : ℝ)) ≤ 3*Real.log (2*(Y : ℝ)) := by
  have hr' : (r : ℝ) ≤ Y := Nat.cast_le.mpr hrY
  have hq' : (q : ℝ) ≤ Y := Nat.cast_le.mpr hqY
  have hy' : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hh := mul_le_mul hr' hq' (by positivity : (0:ℝ) ≤ q) hy'.le
  have hp := mul_le_mul_of_nonneg_right hh (show (0:ℝ) ≤ Y by positivity)
  calc
    Real.log (2 * ((r*q : ℕ) : ℝ) * (Y : ℝ)) ≤ Real.log ((2*(Y:ℝ))^3) := by
      apply Real.log_le_log (by push_cast; positivity)
      push_cast
      nlinarith only [hp, pow_nonneg hy'.le 3]
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Integrating the continuous fiber discrepancy costs one character mean square, averaged
by character Parseval; no loss by the number of characters remains. -/
theorem shortUnitDiscrepancy_interval_bound {C : ℝ}
    (hC : 0 < C)
    (ht : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (ξ : ℝ),
      2 ≤ Y → 1/(Y:ℝ) ≤ ξ → ξ ≤ 1/2 →
      (∫ t in -ξ..ξ, ‖shortPrimeTwistedRemainder χ Y t‖^2) ≤
        C*(Y:ℝ)*ξ*Real.log (2*(d:ℝ)*Y)^2)
    {r q Y : ℕ} (hr : 0 < r) (hq : 0 < q) (hrY : r ≤ Y) (hqY : q ≤ Y)
    (hY : 2 ≤ Y) [NeZero (r * q)] {δ : ℝ} (hδ : (r:ℝ)/Y ≤ δ) (hδ₂ : δ ≤ 1/2) :
    (∫ β in -δ..δ, ∑ u ∈ zmodUnitsFinset (r*q), ‖shortUnitDiscrepancy r q Y β u‖^2) ≤
      9*C*(Y:ℝ)*δ*Real.log (2*(Y:ℝ))^2 := by
  let d := r*q
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hr₁ : (1:ℝ)≤r := Nat.one_le_cast.mpr hr
  have hY' : (0:ℝ)<Y := Nat.cast_pos.mpr (by omega)
  have hδ₀ : 0 ≤ δ := (by positivity : 0 ≤ (r:ℝ)/Y).trans hδ
  have hξ : 1/(Y:ℝ) ≤ δ/r := (le_div_iff₀ hr').2 (by
    rw [one_div, inv_mul_eq_div]; exact hδ)
  have hξ₂ : δ/r ≤ 1/2 := (div_le_self hδ₀ hr₁).trans hδ₂
  let L := Real.log (2*(Y:ℝ))
  let P := 9*C*(Y:ℝ)*δ*L^2
  have hdpos : 0 < d := Nat.mul_pos hr hq
  have hφ : (0:ℝ)<d.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hdpos)
  have hlog : 0 ≤ Real.log (2*(d:ℝ)*Y) :=
    Real.log_nonneg (by exact_mod_cast (Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) hdpos)
      (show 0 < Y by omega) : 1 ≤ 2*d*Y))
  have hlog' : Real.log (2*(d:ℝ)*Y) ≤ 3*L := short_log_modulus_bound hr hq hrY hqY hY
  have hχ (χ : DirichletCharacter ℂ d) :
      (∫ β in -δ..δ, ‖shortPrimeTwistedRemainder χ Y (β/(r:ℝ))‖^2) ≤ P := by
    let f := fun t => ‖shortPrimeTwistedRemainder χ Y t‖^2
    have hs := intervalIntegral.integral_comp_div (f := f) (a := -δ) (b := δ) hr'.ne'
    change (∫ β in -δ..δ, f (β/(r:ℝ))) = (r:ℝ) • ∫ t in (-δ)/(r:ℝ)..δ/(r:ℝ), f t at hs
    change (∫ β in -δ..δ, f (β/(r:ℝ))) ≤ P
    rw [hs, neg_div, smul_eq_mul]
    have he := ht Y d χ (δ/r) hY hξ hξ₂
    change (∫ t in -(δ/(r:ℝ))..δ/(r:ℝ), f t) ≤
      C*(Y:ℝ)*(δ/(r:ℝ))*Real.log (2*(d:ℝ)*Y)^2 at he
    refine (mul_le_mul_of_nonneg_left he hr'.le).trans ?_
    have hlogs := pow_le_pow_left₀ hlog hlog' 2
    calc _ ≤ (r:ℝ)*(C*(Y:ℝ)*(δ/r)*(3*L)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogs (by positivity)) hr'.le
      _ = P := by dsimp [P]; field_simp; ring
  have hident (β : ℝ) :
      (∑ u ∈ zmodUnitsFinset d, ‖shortUnitDiscrepancy r q Y β u‖^2) =
        (1/(d.totient:ℝ))*∑ χ : DirichletCharacter ℂ d,
          ‖shortPrimeTwistedRemainder χ Y (β/r)‖^2 := by
    rw [mul_parseval_units hdpos]
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [shortUnitDiscrepancy_character hr hq]
  change (∫ β in -δ..δ, ∑ u ∈ zmodUnitsFinset d, ‖shortUnitDiscrepancy r q Y β u‖^2) ≤ P
  simp_rw [hident]
  rw [intervalIntegral.integral_const_mul, intervalIntegral_finset_sum]
  · calc _ ≤ (1/(d.totient:ℝ)) * ∑ _χ : DirichletCharacter ℂ d, P :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hχ χ) (by positivity)
      _ = (1/(d.totient:ℝ)) * (P * ∑ _χ : DirichletCharacter ℂ d, (1 : ℝ)) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => (mul_one P).symm
      _ = P := by rw [sum_one_dirichletChar d]; field_simp
  · intro χ _
    have hf : Continuous (shortPrimeTwistedRemainder χ Y) := continuous_shortTwistedRemainderWith .. 
    exact (hf.norm.pow 2 |>.comp (continuous_id.div_const _)).intervalIntegrable _ _

/-- A class average over one rational arc. With `δ=1/(qQ)`, the numerator
`q` from the fiber size cancels the arc width. -/
theorem shortLocalRemainder_avg_interval_bound {C : ℝ}
    (hC : 0 < C)
    (ht : ∀ (Y d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (ξ : ℝ),
      2 ≤ Y → 1/(Y:ℝ) ≤ ξ → ξ ≤ 1/2 →
      (∫ t in -ξ..ξ, ‖shortPrimeTwistedRemainder χ Y t‖^2) ≤
        C*(Y:ℝ)*ξ*Real.log (2*(d:ℝ)*Y)^2)
    {r q a Y : ℕ} (hr : 0 < r) (hq : 0 < q) (hrY : r ≤ Y) (hqY : q ≤ Y)
    (hY : 2 ≤ Y) [NeZero (r * q)] {δ : ℝ} (hδ : (r:ℝ)/Y ≤ δ) (hδ₂ : δ ≤ 1/2) :
    (∫ β in -δ..δ, (1/(r.totient:ℝ)) *
      ∑ b ∈ coprimeClasses r, ‖shortLocalRemainder r b Y a q β‖^2) ≤
        (18*C+4) * ((q:ℝ)*(Y:ℝ)/r.totient) * δ * Real.log (2*(Y:ℝ))^2 := by
  let L := Real.log (2*(Y:ℝ))
  let F (β : ℝ) := ∑ u ∈ zmodUnitsFinset (r*q), ‖shortUnitDiscrepancy r q Y β u‖^2
  let R (β : ℝ) := (1/(r.totient:ℝ)) *
    ∑ b ∈ coprimeClasses r, ‖shortLocalRemainder r b Y a q β‖^2
  let p : ℝ := r.totient
  have hp : 0 < p := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hδ₀ : 0 ≤ δ := (by positivity : 0 ≤ (r:ℝ)/Y).trans hδ
  have hF : Continuous F := continuous_sum_finset _ fun u _ =>
    (continuous_shortUnitDiscrepancy r q Y u).norm.pow 2
  have hR : Continuous R := continuous_const.mul (continuous_sum_finset (coprimeClasses r) fun b _ =>
    (continuous_shortLocalRemainder r b Y a q).norm.pow 2)
  have hpoint (β : ℝ) : R β ≤ (2*(q:ℝ)/p)*F β + 2*L^2 := by
    let D (b : ℕ) := ∑ u ∈ charSupp r q b,
      e ((a:ℝ)*((u.val/r:ℕ):ℝ)/q) * shortUnitDiscrepancy r q Y β u
    have hper (b : ℕ) (hb : b ∈ coprimeClasses r) :
        ‖shortLocalRemainder r b Y a q β‖^2 ≤ 2*‖D b‖^2 + 2*L^2 := by
      have ht' := mem_coprimeClasses.mp hb
      have h := shortLocalRemainder_le (a := a) hr hq hqY hY ht'.1 ht'.2 β
      change ‖shortLocalRemainder r b Y a q β‖ ≤ ‖D b‖+L at h
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith only [hs, sq_nonneg (‖D b‖-L)]
    have hfactor : (((r*q).totient:ℝ)/p^2) ≤ (q:ℝ)/p := by
      have h := totient_mul_le_mul_totient r q hr hq
      have hn : ((r*q).totient:ℝ) ≤ (q:ℝ)*p := by dsimp [p]; exact_mod_cast h
      calc _ ≤ (q:ℝ)*p/p^2 := div_le_div_of_nonneg_right hn (by positivity)
        _ = _ := by field_simp
    have hF₀ : 0 ≤ F β := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hfiber := fiber_sq_le hr hq (fun u => shortUnitDiscrepancy r q Y β u)
      (fun _ u => e ((a:ℝ)*((u.val/r:ℕ):ℝ)/q)) (fun _ _ _ _ => by rw [norm_e])
    change (1/p)*∑ b ∈ coprimeClasses r, ‖D b‖^2 ≤ _ at hfiber
    calc R β ≤ (1/p)*∑ b ∈ coprimeClasses r, (2*‖D b‖^2 + 2*L^2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by positivity)
      _ = 2*((1/p)*∑ b ∈ coprimeClasses r, ‖D b‖^2) + 2*L^2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, card_coprimeClasses]
        dsimp [p]
        field_simp
      _ ≤ (2*(q:ℝ)/p)*F β + 2*L^2 := by
        have he := hfiber.trans (mul_le_mul_of_nonneg_right hfactor hF₀)
        change _ ≤ (q:ℝ)/p * F β at he
        convert add_le_add_right (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤2)) (2*L^2) using 1 <;> ring
  have hconst : IntervalIntegrable (fun _ : ℝ => 2*L^2) volume (-δ) δ :=
    continuous_const.intervalIntegrable _ _
  have hmon : (∫ β in -δ..δ, R β) ≤ ∫ β in -δ..δ, (2*(q:ℝ)/p)*F β + 2*L^2 :=
    intervalIntegral.integral_mono_on (μ := volume) (show -δ ≤ δ by linarith)
    (hR.intervalIntegrable _ _) (((hF.const_mul _).intervalIntegrable _ _).add hconst)
    (fun β _ => hpoint β)
  rw [intervalIntegral.integral_add ((hF.const_mul _).intervalIntegrable _ _) hconst,
    intervalIntegral.integral_const, smul_eq_mul] at hmon
  rw [show (∫ β in -δ..δ, (2*(q:ℝ)/p)*F β) =
    (2*(q:ℝ)/p) * ∫ β in -δ..δ, F β from intervalIntegral.integral_const_mul _ F] at hmon
  have hF' : (∫ β in -δ..δ, F β) ≤ 9*C*(Y:ℝ)*δ*L^2 :=
    shortUnitDiscrepancy_interval_bound hC ht hr hq hrY hqY hY hδ hδ₂
  have hsize : 1 ≤ (q:ℝ)*Y/p := by
    apply (le_div_iff₀ hp).2
    have hq' : (1:ℝ)≤q := Nat.one_le_cast.mpr hq
    have hpY : p≤(Y:ℝ) := by dsimp [p]; exact_mod_cast (Nat.totient_le r).trans hrY
    have h := mul_le_mul_of_nonneg_right hq' (show (0:ℝ) ≤ Y by positivity)
    linarith only [hpY,h]
  have hmul := mul_le_mul_of_nonneg_left hF' (show 0 ≤ 2*(q:ℝ)/p by positivity)
  have hs := mul_le_mul_of_nonneg_right hsize (show 0 ≤ 4*δ*L^2 by positivity)
  change (∫ β in -δ..δ, R β) ≤ (18*C+4)*((q:ℝ)*Y/p)*δ*L^2
  simp only [div_eq_mul_inv] at hmon hmul hs ⊢
  linarith only [hmon,hmul,hs]

end FareyGoldbach
