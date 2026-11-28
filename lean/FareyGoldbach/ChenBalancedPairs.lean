import FareyGoldbach.ChenAPSwitchingFibers

/-! # Balanced semiprime pairs and their reflected progression carriers -/

open Finset
open scoped Classical

namespace FareyGoldbach

/-- A prime, or a product of two primes satisfying the indicated power inequality. -/
def IsAlmostPrimeTwoBounded (a : ℝ) (m : ℕ) : Prop :=
  m.Prime ∨ ∃ r q : ℕ, r.Prime ∧ q.Prime ∧ m=r*q ∧ (r:ℝ)≤(q:ℝ)^(a-1)

def chenBalancedPairs (N L : ℕ) : Finset (ℕ×ℕ) :=
  (N.primesLE ×ˢ N.primesLE).filter (fun x => L<x.1 ∧ x.1≤x.2 ∧ x.1*x.2<N)

def chenBalancedB (N L : ℕ) : Finset ℕ :=
  (chenBalancedPairs N L).image (fun x => N-x.1*x.2)

def chenAPBalancedB (N r b L : ℕ) : Finset ℕ :=
  (chenBalancedB N L).filter (fun p => (N-p)%r=b%r)

noncomputable def chenAPBoundedRepresentations (N r b₁ b₂ : ℕ) (a : ℝ) : Finset ℕ :=
  (chenAPRepresentations N r b₁ b₂).filter (fun p => IsAlmostPrimeTwoBounded a (N-p))

theorem chenBalancedPairs_product_lt {N L : ℕ} {x : ℕ×ℕ}
    (hx : x∈chenBalancedPairs N L) : x.1*x.2<N := (mem_filter.mp hx).2.2.2

theorem chenBalancedPairs_product_pos {N L : ℕ} {x : ℕ×ℕ}
    (hx : x∈chenBalancedPairs N L) : 0<x.1*x.2 := by
  obtain ⟨hu,hv⟩ := mem_product.mp (mem_filter.mp hx).1
  exact Nat.mul_pos (Nat.mem_primesLE.mp hu).2.pos (Nat.mem_primesLE.mp hv).2.pos

theorem chenBalancedPairs_rough {N L p : ℕ} {x : ℕ×ℕ}
    (hx : x∈chenBalancedPairs N L) (hp : p.Prime) (hd : p∣x.1*x.2) : L<p := by
  obtain ⟨hs,hL,huv,_⟩ := mem_filter.mp hx
  obtain ⟨hu,hv⟩ := mem_product.mp hs
  rcases hp.dvd_mul.mp hd with h|h
  · rwa [(Nat.prime_dvd_prime_iff_eq hp (Nat.mem_primesLE.mp hu).2).mp h]
  · rw [(Nat.prime_dvd_prime_iff_eq hp (Nat.mem_primesLE.mp hv).2).mp h]
    exact hL.trans_le huv

private theorem minFac_ordered_prime_mul {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
    (huv : u≤v) : (u*v).minFac=u := by
  have hmin := Nat.minFac_le_of_dvd hu.two_le (Nat.dvd_mul_right u v)
  have hn := Nat.le_mul_of_pos_right u hv.pos
  have h2 := hu.two_le
  have hp := Nat.minFac_prime (show u*v≠1 by omega)
  rcases hp.dvd_mul.mp (Nat.minFac_dvd (u*v)) with h|h
  · exact (Nat.prime_dvd_prime_iff_eq hp hu).mp h
  · have he := (Nat.prime_dvd_prime_iff_eq hp hv).mp h
    omega

theorem chenBalancedPairs_product_injective (N L : ℕ) :
    Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) (chenBalancedPairs N L) := by
  rintro ⟨u,v⟩ hx ⟨s,t⟩ hy he
  obtain ⟨hs,_,huv,_⟩ := mem_filter.mp hx
  obtain ⟨ht,_,hst,_⟩ := mem_filter.mp hy
  obtain ⟨hu,hv⟩ := mem_product.mp hs
  obtain ⟨hs,ht⟩ := mem_product.mp ht
  have h₁ := minFac_ordered_prime_mul (Nat.mem_primesLE.mp hu).2 (Nat.mem_primesLE.mp hv).2 huv
  have h₂ := minFac_ordered_prime_mul (Nat.mem_primesLE.mp hs).2 (Nat.mem_primesLE.mp ht).2 hst
  change u*v=s*t at he
  have hus : u=s := h₁.symm.trans ((congrArg Nat.minFac he).trans h₂)
  subst s
  exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (Nat.mem_primesLE.mp hu).2.pos he)

theorem chenBalancedPairs_reflect_injective (N L : ℕ) :
    Set.InjOn (fun x : ℕ×ℕ => N-x.1*x.2) (chenBalancedPairs N L) := by
  intro x hx y hy he
  apply chenBalancedPairs_product_injective N L hx hy
  have h₁ := chenBalancedPairs_product_lt hx
  have h₂ := chenBalancedPairs_product_lt hy
  change N-x.1*x.2=N-y.1*y.2 at he
  change x.1*x.2=y.1*y.2
  omega

theorem chenBalancedB_card_eq_pairs (N L : ℕ) :
    (chenBalancedB N L).card=(chenBalancedPairs N L).card :=
  card_image_of_injOn (chenBalancedPairs_reflect_injective N L)

theorem chenBalancedB_card_divisible_pair_filter (N L d : ℕ) :
    (chenDivisible (chenBalancedB N L) d).card =
      ((chenBalancedPairs N L).filter (fun x => (x.1*x.2)%d=N%d)).card := by
  rw [chenDivisible,chenBalancedB,filter_image]
  rw [card_image_of_injOn ((chenBalancedPairs_reflect_injective N L).mono (filter_subset ..))]
  congr 1
  ext x
  simp only [mem_filter]
  refine and_congr_right fun hx => ?_
  exact (Nat.modEq_iff_dvd' (chenBalancedPairs_product_lt hx).le).symm

theorem chenAPBalancedB_eq_pair_filter_image (N r b L : ℕ) :
    chenAPBalancedB N r b L =
      ((chenBalancedPairs N L).filter (fun x => (x.1*x.2)%r=b%r)).image
        (fun x => N-x.1*x.2) := by
  rw [chenAPBalancedB,chenBalancedB,filter_image]
  congr 1
  ext x
  simp only [mem_filter]
  refine and_congr_right fun hx => ?_
  simp only [Nat.sub_sub_self (chenBalancedPairs_product_lt hx).le]

theorem chenAPBalancedB_card_eq_pair_filter (N r b L : ℕ) :
    (chenAPBalancedB N r b L).card =
      ((chenBalancedPairs N L).filter (fun x => (x.1*x.2)%r=b%r)).card := by
  rw [chenAPBalancedB_eq_pair_filter_image]
  exact card_image_of_injOn ((chenBalancedPairs_reflect_injective N L).mono (filter_subset ..))

theorem chenAPBalancedB_card_divisible_pair_filter (N r b L d : ℕ) :
    (chenDivisible (chenAPBalancedB N r b L) d).card =
      ((chenBalancedPairs N L).filter
        (fun x => (x.1*x.2)%r=b%r ∧ (x.1*x.2)%d=N%d)).card := by
  rw [chenDivisible,chenAPBalancedB_eq_pair_filter_image,filter_image]
  rw [card_image_of_injOn ((chenBalancedPairs_reflect_injective N L).mono
    (show _⊆chenBalancedPairs N L from (filter_subset ..).trans (filter_subset ..)))]
  congr 1
  ext x
  simp only [mem_filter,and_assoc]
  refine and_congr_right fun hx => and_congr_right fun _ => ?_
  exact (Nat.modEq_iff_dvd' (chenBalancedPairs_product_lt hx).le).symm

end FareyGoldbach
