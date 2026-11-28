import FareyGoldbach.ChenAPSwitching
import FareyGoldbach.ChenSwitchingPairs

/-! # Progression and divisibility conditions on the two switching coordinates -/

open Finset
open scoped Classical

namespace FareyGoldbach

theorem chenAPUnrestrictedB_eq_pair_filter_image (N r b z y : ℕ) :
    chenAPUnrestrictedB N r b z y =
      ((chenSwitchPairs N z y).filter (fun x => (x.1*x.2)%r=b%r)).image
        (fun x => N-x.1*x.2) := by
  rw [chenAPUnrestrictedB,chenUnrestrictedB_eq_pair_image,filter_image]
  congr 1
  ext x
  simp only [mem_filter]
  refine and_congr_right fun hx => ?_
  simp only [Nat.sub_sub_self (chenSwitchPairs_product_lt hx).le]

theorem chenAPUnrestrictedB_card_eq_pair_filter (N r b z y : ℕ) :
    (chenAPUnrestrictedB N r b z y).card =
      ((chenSwitchPairs N z y).filter (fun x => (x.1*x.2)%r=b%r)).card := by
  rw [chenAPUnrestrictedB_eq_pair_filter_image]
  exact card_image_of_injOn ((chenSwitchPairs_reflect_injective N z y).mono (filter_subset ..))

theorem chenAPUnrestrictedB_card_divisible_pair_filter (N r b z y d : ℕ) :
    (chenDivisible (chenAPUnrestrictedB N r b z y) d).card =
      ((chenSwitchPairs N z y).filter
        (fun x => (x.1*x.2)%r=b%r ∧ (x.1*x.2)%d=N%d)).card := by
  rw [chenDivisible,chenAPUnrestrictedB_eq_pair_filter_image,filter_image]
  rw [card_image_of_injOn ((chenSwitchPairs_reflect_injective N z y).mono
    (show _⊆chenSwitchPairs N z y from (filter_subset ..).trans (filter_subset ..)))]
  congr 1
  ext x
  simp only [mem_filter,and_assoc]
  refine and_congr_right fun hx => and_congr_right fun _ => ?_
  exact (Nat.modEq_iff_dvd' (chenSwitchPairs_product_lt hx).le).symm

theorem chenSwitchPairs_coprime_of_modulus_lt_cutoff {N z y r : ℕ} (hr : 0<r) (hrz : r<z)
    {x : ℕ×ℕ} (hx : x∈chenSwitchPairs N z y) : (x.1*x.2).Coprime r := by
  by_contra h
  obtain ⟨p,hp,hm,hd⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (not_lt_of_ge (chenSwitchPairs_rough hx hp hm)) ((Nat.le_of_dvd hr hd).trans_lt hrz)

end FareyGoldbach
