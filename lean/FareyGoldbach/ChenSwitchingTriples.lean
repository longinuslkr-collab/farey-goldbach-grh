import FareyGoldbach.ChenDistributionInterfaces

/-! # The ordered triples in Chen's switched carrier -/

namespace FareyGoldbach

open Finset
open scoped Classical

def chenTripleProduct (t : ℕ×ℕ×ℕ) : ℕ := t.1*t.2.1*t.2.2

def chenSwitchTriples (N z y : ℕ) : Finset (ℕ×ℕ×ℕ) :=
  (N.primesLE ×ˢ (N.primesLE ×ˢ N.primesLE)).filter fun t =>
    z≤t.1 ∧ t.1<y ∧ y≤t.2.1 ∧ t.2.1≤t.2.2 ∧ chenTripleProduct t<N

theorem mem_chenSwitchTriples {N z y u v w : ℕ} :
    (u,v,w)∈chenSwitchTriples N z y ↔ u.Prime ∧ v.Prime ∧ w.Prime ∧
      z≤u ∧ u<y ∧ y≤v ∧ v≤w ∧ u*v*w<N := by
  constructor
  · intro h
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp h
    obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hp
    obtain ⟨h₂,h₃⟩ := Finset.mem_product.mp h₂
    exact ⟨(Nat.mem_primesLE.mp h₁).2,(Nat.mem_primesLE.mp h₂).2,
      (Nat.mem_primesLE.mp h₃).2,ht⟩
  · rintro ⟨hu,hv,hw,hz,hy,hv',hw',hlt⟩
    have hwP := Nat.le_mul_of_pos_left w (Nat.mul_pos hu.pos hv.pos)
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨show u≤N by omega,hu⟩,
      Finset.mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨show v≤N by omega,hv⟩,
        Nat.mem_primesLE.mpr ⟨hwP.trans hlt.le,hw⟩⟩⟩,hz,hy,hv',hw',hlt⟩

private theorem chenTriple_factors {u v w : ℕ} (hu : u.Prime) (hv : v.Prime) (hw : w.Prime)
    (huv : u≤v) (hvw : v≤w) : [u,v,w] = (u*v*w).primeFactorsList := by
  have hs : [u,v,w].Pairwise (·≤·) := by simp [huv,hvw,huv.trans hvw]
  apply List.Perm.eq_of_pairwise' hs (Nat.primeFactorsList_sorted _).pairwise
  apply Nat.primeFactorsList_unique
  · simp [mul_assoc]
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl <;> assumption

theorem chenTripleProduct_injOn (N z y : ℕ) :
    Set.InjOn chenTripleProduct (chenSwitchTriples N z y) := by
  rintro ⟨u,v,w⟩ h₁ ⟨a,b,c⟩ h₂ he
  obtain ⟨hu,hv,hw,_,huy,hyv,hvw,_⟩ := mem_chenSwitchTriples.mp h₁
  obtain ⟨ha,hb,hc,_,hay,hyb,hbc,_⟩ := mem_chenSwitchTriples.mp h₂
  change u*v*w=a*b*c at he
  have hlist := (chenTriple_factors hu hv hw (huy.le.trans hyv) hvw).trans
    ((congrArg Nat.primeFactorsList he).trans (chenTriple_factors ha hb hc (hay.le.trans hyb) hbc).symm)
  simpa using hlist

theorem chenUnrestrictedB_eq_triple_image (N z y : ℕ) :
    chenUnrestrictedB N z y = (chenSwitchTriples N z y).image (fun t => N-chenTripleProduct t) := by
  ext b
  constructor
  · intro hb
    obtain ⟨_,u,v,w,hu,hv,hw,hz,hy,hv',hw',hlt,rfl⟩ := mem_filter.mp hb
    exact mem_image.mpr ⟨(u,v,w),mem_chenSwitchTriples.mpr ⟨hu,hv,hw,hz,hy,hv',hw',hlt⟩,rfl⟩
  · intro hb
    obtain ⟨⟨u,v,w⟩,ht,rfl⟩ := mem_image.mp hb
    obtain ⟨hu,hv,hw,hz,hy,hv',hw',hlt⟩ := mem_chenSwitchTriples.mp ht
    exact mem_filter.mpr ⟨mem_range.mpr (by change N-u*v*w<N+1; omega),
      u,v,w,hu,hv,hw,hz,hy,hv',hw',hlt,rfl⟩

theorem chenUnrestrictedB_card_eq_triples (N z y : ℕ) :
    (chenUnrestrictedB N z y).card = (chenSwitchTriples N z y).card := by
  rw [chenUnrestrictedB_eq_triple_image]
  apply card_image_of_injOn
  intro x hx y' hy he
  apply chenTripleProduct_injOn N z y hx hy
  have hx' := (mem_filter.mp hx).2.2.2.2.2
  have hy' := (mem_filter.mp hy).2.2.2.2.2
  change N-chenTripleProduct x=N-chenTripleProduct y' at he
  omega

end FareyGoldbach
