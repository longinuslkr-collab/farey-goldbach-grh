import FareyGoldbach.ChenSwitchingTriples

/-! # The two variables in the switched bilinear sum -/

open Finset
open scoped Classical

namespace FareyGoldbach

def chenSwitchV (m : ℕ) : ℕ := m / m.minFac

def chenSwitchActive (z y m : ℕ) : Prop :=
  m.minFac.Prime ∧ (chenSwitchV m).Prime ∧ z≤m.minFac ∧ m.minFac<y ∧ y≤chenSwitchV m

def chenSwitchPairs (N z y : ℕ) : Finset (ℕ × ℕ) :=
  (chenSwitchTriples N z y).image (fun t => (t.1*t.2.1,t.2.2))

theorem chenSwitch_minFac_mul {u v : ℕ} (hu : u.Prime) (hv : v.Prime) (huv : u<v) :
    (u*v).minFac = u := by
  have hmin := Nat.minFac_le_of_dvd hu.two_le (Nat.dvd_mul_right u v)
  have hp := Nat.minFac_prime (show u*v≠1 by
    have := Nat.le_mul_of_pos_right u hv.pos
    have := hu.two_le
    omega)
  rcases hp.dvd_mul.mp (Nat.minFac_dvd (u*v)) with h|h
  · exact (Nat.prime_dvd_prime_iff_eq hp hu).mp h
  · have := (Nat.prime_dvd_prime_iff_eq hp hv).mp h
    omega

theorem mem_chenSwitchPairs_iff {N z y m w : ℕ} :
    (m,w)∈chenSwitchPairs N z y ↔
      0<m ∧ chenSwitchActive z y m ∧ w.Prime ∧ chenSwitchV m≤w ∧ m*w<N := by
  constructor
  · intro h
    obtain ⟨⟨u,v,s⟩,ht,he⟩ := mem_image.mp h
    have hm : u*v=m := congrArg Prod.fst he
    have hw : s=w := congrArg Prod.snd he
    subst m
    subst w
    obtain ⟨hu,hv,hs,hz,huy,hyv,hvs,hN⟩ := mem_chenSwitchTriples.mp ht
    have hfac := chenSwitch_minFac_mul hu hv (huy.trans_le hyv)
    have hV : chenSwitchV (u*v)=v := by rw [chenSwitchV,hfac,Nat.mul_div_cancel_left _ hu.pos]
    exact ⟨Nat.mul_pos hu.pos hv.pos, by simpa [chenSwitchActive,hfac,hV] using
      (show u.Prime ∧ v.Prime ∧ z≤u ∧ u<y ∧ y≤v from ⟨hu,hv,hz,huy,hyv⟩),
      hs,by simpa only [hV] using hvs,hN⟩
  · rintro ⟨_,⟨hu,hv,hz,huy,hyv⟩,hw,hvw,hN⟩
    have hprod : m.minFac * chenSwitchV m = m := Nat.mul_div_cancel' (Nat.minFac_dvd m)
    refine mem_image.mpr ⟨(m.minFac,chenSwitchV m,w),mem_chenSwitchTriples.mpr
      ⟨hu,hv,hw,hz,huy,hyv,hvw,by simpa only [hprod] using hN⟩,?_⟩
    exact Prod.ext hprod rfl

theorem chenSwitchPairs_product_lt {N z y : ℕ} {x : ℕ×ℕ} (hx : x∈chenSwitchPairs N z y) :
    x.1*x.2<N := (mem_chenSwitchPairs_iff.mp hx).2.2.2.2

theorem chenSwitchPairs_product_pos {N z y : ℕ} {x : ℕ×ℕ} (hx : x∈chenSwitchPairs N z y) :
    0<x.1*x.2 := by
  obtain ⟨hm,_,hw,_,_⟩ := mem_chenSwitchPairs_iff.mp hx
  exact Nat.mul_pos hm hw.pos

theorem chenSwitchPairs_rough {N z y : ℕ} {x : ℕ×ℕ} (hx : x∈chenSwitchPairs N z y)
    {p : ℕ} (hp : p.Prime) (hpx : p∣x.1*x.2) : z≤p := by
  obtain ⟨⟨u,v,w⟩, ht, rfl⟩ := mem_image.mp hx
  obtain ⟨hu,hv,hw,hzu,huy,hyv,hvw,_⟩ := mem_chenSwitchTriples.mp ht
  change p∣u*v*w at hpx
  rcases hp.dvd_mul.mp hpx with hm|h
  · rcases hp.dvd_mul.mp hm with h|h
    · rwa [(Nat.prime_dvd_prime_iff_eq hp hu).mp h]
    · rw [(Nat.prime_dvd_prime_iff_eq hp hv).mp h]
      exact hzu.trans (huy.le.trans hyv)
  · rw [(Nat.prime_dvd_prime_iff_eq hp hw).mp h]
    exact hzu.trans (huy.le.trans (hyv.trans hvw))

theorem chenSwitchPairs_product_injective (N z y : ℕ) :
    Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) (chenSwitchPairs N z y) := by
  intro x hx x' hx' he
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hx
  obtain ⟨t',ht',rfl⟩ := mem_image.mp hx'
  exact congrArg (fun v : ℕ×ℕ×ℕ => (v.1*v.2.1,v.2.2)) (chenTripleProduct_injOn N z y ht ht' he)

theorem chenSwitchPairs_reflect_injective (N z y : ℕ) :
    Set.InjOn (fun x : ℕ×ℕ => N-x.1*x.2) (chenSwitchPairs N z y) := by
  intro x hx x' hx' he
  apply chenSwitchPairs_product_injective N z y hx hx'
  have hl := chenSwitchPairs_product_lt hx
  have hr := chenSwitchPairs_product_lt hx'
  change N-x.1*x.2=N-x'.1*x'.2 at he
  change x.1*x.2=x'.1*x'.2
  omega

theorem chenUnrestrictedB_eq_pair_image (N z y : ℕ) :
    chenUnrestrictedB N z y = (chenSwitchPairs N z y).image (fun x => N-x.1*x.2) := by
  rw [chenUnrestrictedB_eq_triple_image,chenSwitchPairs,Finset.image_image]
  rfl

theorem chenUnrestrictedB_card_eq_pairs (N z y : ℕ) :
    (chenUnrestrictedB N z y).card = (chenSwitchPairs N z y).card := by
  rw [chenUnrestrictedB_eq_pair_image]
  exact card_image_of_injOn (chenSwitchPairs_reflect_injective N z y)

theorem chenSwitchPairs_card_progression (N z y d : ℕ) :
    (chenDivisible (chenUnrestrictedB N z y) d).card =
      ((chenSwitchPairs N z y).filter (fun x => (x.1*x.2)%d=N%d)).card := by
  classical
  let F := (chenSwitchPairs N z y).filter (fun x => (x.1*x.2)%d=N%d)
  have he : chenDivisible (chenUnrestrictedB N z y) d = F.image (fun x => N-x.1*x.2) := by
    ext b
    rw [chenDivisible,chenUnrestrictedB_eq_pair_image]
    simp only [F,mem_filter,mem_image]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hd⟩
      exact ⟨x,⟨hx,(Nat.modEq_iff_dvd' (chenSwitchPairs_product_lt hx).le).mpr hd⟩,rfl⟩
    · rintro ⟨x,⟨hx,hmod⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(Nat.modEq_iff_dvd' (chenSwitchPairs_product_lt hx).le).mp hmod⟩
  rw [he]
  apply card_image_of_injOn
  intro x hx x' hx' hh
  exact chenSwitchPairs_reflect_injective N z y (mem_filter.mp hx).1 (mem_filter.mp hx').1 hh

end FareyGoldbach
