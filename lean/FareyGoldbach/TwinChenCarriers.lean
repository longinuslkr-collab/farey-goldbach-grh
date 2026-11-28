import FareyGoldbach.ChenBalancedSwitching

/-! # The shifted-prime and switched pair carriers for Chen's twin-prime theorem -/

open Finset
open scoped Classical

namespace FareyGoldbach

def twinChenAPA (X r b : ℕ) : Finset ℕ :=
  (X.primesLE.filter (fun p => p%r=b%r)).image (fun p => p+2)

noncomputable def twinChenRepresentations (X r b : ℕ) : Finset ℕ :=
  X.primesLE.filter (fun p => p%r=b%r ∧ IsAlmostPrimeTwo (p+2))

noncomputable def twinChenBoundedRepresentations (X r b : ℕ) (α : ℝ) : Finset ℕ :=
  X.primesLE.filter (fun p => p%r=b%r ∧ IsAlmostPrimeTwoBounded α (p+2))

def twinChenUnrestrictedB (M z y : ℕ) : Finset ℕ :=
  (chenSwitchPairs M z y).image (fun x => x.1*x.2-2)

def twinChenAPUnrestrictedB (M r b z y : ℕ) : Finset ℕ :=
  (twinChenUnrestrictedB M z y).filter (fun p => (p+2)%r=(b+2)%r)

def twinChenBalancedB (M L : ℕ) : Finset ℕ :=
  (chenBalancedPairs M L).image (fun x => x.1*x.2-2)

def twinChenAPBalancedB (M r b L : ℕ) : Finset ℕ :=
  (twinChenBalancedB M L).filter (fun p => (p+2)%r=(b+2)%r)

theorem chenSwitchPairs_product_ge_two {M z y : ℕ} {x : ℕ×ℕ} (hx : x∈chenSwitchPairs M z y) :
    2≤x.1*x.2 := by
  obtain ⟨hm,_,hw,_,_⟩ := mem_chenSwitchPairs_iff.mp hx
  exact hw.two_le.trans (Nat.le_mul_of_pos_left _ hm)

theorem chenBalancedPairs_product_ge_two {M L : ℕ} {x : ℕ×ℕ} (hx : x∈chenBalancedPairs M L) :
    2≤x.1*x.2 := by
  obtain ⟨hu,hv⟩ := mem_product.mp (mem_filter.mp hx).1
  exact (Nat.mem_primesLE.mp hu).2.two_le.trans
    (Nat.le_mul_of_pos_right _ (Nat.mem_primesLE.mp hv).2.pos)

private theorem shift_injective {P : Finset (ℕ×ℕ)} (h₂ : ∀ x∈P, 2≤x.1*x.2)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P) :
    Set.InjOn (fun x : ℕ×ℕ => x.1*x.2-2) P := by
  intro x hx x' hx' he
  apply hinj hx hx'
  change x.1*x.2-2=x'.1*x'.2-2 at he
  change x.1*x.2=x'.1*x'.2
  have h := h₂ x hx
  have h' := h₂ x' hx'
  omega

private theorem shift_filter_image (P : Finset (ℕ×ℕ)) (h₂ : ∀ x∈P, 2≤x.1*x.2)
    (r b : ℕ) :
    (P.image (fun x => x.1*x.2-2)).filter (fun t => (t+2)%r=(b+2)%r) =
      (P.filter (fun x => (x.1*x.2)%r=(b+2)%r)).image (fun x => x.1*x.2-2) := by
  rw [filter_image]
  congr 1
  ext x
  simp only [mem_filter]
  refine and_congr_right fun hx => ?_
  rw [Nat.sub_add_cancel (h₂ x hx)]

private theorem shift_card (P : Finset (ℕ×ℕ)) (h₂ : ∀ x∈P, 2≤x.1*x.2)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P) (r b : ℕ) :
    ((P.image (fun x => x.1*x.2-2)).filter (fun t => (t+2)%r=(b+2)%r)).card =
      (P.filter (fun x => (x.1*x.2)%r=(b+2)%r)).card := by
  rw [shift_filter_image P h₂]
  exact card_image_of_injOn ((shift_injective h₂ hinj).mono (filter_subset ..))

private theorem shift_divisible_card (P : Finset (ℕ×ℕ)) (h₂ : ∀ x∈P, 2≤x.1*x.2)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P) (r b d : ℕ) :
    (chenDivisible ((P.image (fun x => x.1*x.2-2)).filter (fun t => (t+2)%r=(b+2)%r)) d).card =
      (P.filter (fun x => (x.1*x.2)%r=(b+2)%r ∧ (x.1*x.2)%d=2%d)).card := by
  rw [shift_filter_image P h₂,chenDivisible,filter_image]
  rw [card_image_of_injOn ((shift_injective h₂ hinj).mono
    (show _ ⊆ P from (filter_subset ..).trans (filter_subset ..)))]
  congr 1
  ext x
  simp only [mem_filter,and_assoc]
  refine and_congr_right fun hx => and_congr_right fun _ => ?_
  exact (Nat.modEq_iff_dvd' (h₂ x hx)).symm.trans eq_comm

theorem twinChenUnrestrictedB_card_eq_pairs (M z y : ℕ) :
    (twinChenUnrestrictedB M z y).card=(chenSwitchPairs M z y).card :=
  card_image_of_injOn (shift_injective (fun _ hx => chenSwitchPairs_product_ge_two hx)
    (chenSwitchPairs_product_injective M z y))

theorem twinChenBalancedB_card_eq_pairs (M L : ℕ) :
    (twinChenBalancedB M L).card=(chenBalancedPairs M L).card :=
  card_image_of_injOn (shift_injective (fun _ hx => chenBalancedPairs_product_ge_two hx)
    (chenBalancedPairs_product_injective M L))

theorem twinChenAPUnrestrictedB_card_eq_pair_filter (M r b z y : ℕ) :
    (twinChenAPUnrestrictedB M r b z y).card =
      ((chenSwitchPairs M z y).filter (fun x => (x.1*x.2)%r=(b+2)%r)).card :=
  shift_card _ (fun _ hx => chenSwitchPairs_product_ge_two hx) (chenSwitchPairs_product_injective ..) r b

theorem twinChenAPUnrestrictedB_card_divisible_pair_filter (M r b z y d : ℕ) :
    (chenDivisible (twinChenAPUnrestrictedB M r b z y) d).card =
      ((chenSwitchPairs M z y).filter
        (fun x => (x.1*x.2)%r=(b+2)%r ∧ (x.1*x.2)%d=2%d)).card :=
  shift_divisible_card _ (fun _ hx => chenSwitchPairs_product_ge_two hx)
    (chenSwitchPairs_product_injective ..) r b d

theorem twinChenAPBalancedB_card_eq_pair_filter (M r b L : ℕ) :
    (twinChenAPBalancedB M r b L).card =
      ((chenBalancedPairs M L).filter (fun x => (x.1*x.2)%r=(b+2)%r)).card :=
  shift_card _ (fun _ hx => chenBalancedPairs_product_ge_two hx) (chenBalancedPairs_product_injective ..) r b

theorem twinChenAPBalancedB_card_divisible_pair_filter (M r b L d : ℕ) :
    (chenDivisible (twinChenAPBalancedB M r b L) d).card =
      ((chenBalancedPairs M L).filter
        (fun x => (x.1*x.2)%r=(b+2)%r ∧ (x.1*x.2)%d=2%d)).card :=
  shift_divisible_card _ (fun _ hx => chenBalancedPairs_product_ge_two hx)
    (chenBalancedPairs_product_injective ..) r b d

theorem twinChenUnrestrictedB_card_divisible_pair_filter (M z y d : ℕ) :
    (chenDivisible (twinChenUnrestrictedB M z y) d).card =
      ((chenSwitchPairs M z y).filter (fun x => (x.1*x.2)%d=2%d)).card := by
  simpa only [twinChenAPUnrestrictedB,Nat.mod_one,eq_self,true_and,Finset.filter_true] using twinChenAPUnrestrictedB_card_divisible_pair_filter M 1 0 z y d

theorem twinChenBalancedB_card_divisible_pair_filter (M L d : ℕ) :
    (chenDivisible (twinChenBalancedB M L) d).card =
      ((chenBalancedPairs M L).filter (fun x => (x.1*x.2)%d=2%d)).card := by
  simpa only [twinChenAPBalancedB,Nat.mod_one,eq_self,true_and,Finset.filter_true] using twinChenAPBalancedB_card_divisible_pair_filter M 1 0 L d

end FareyGoldbach
