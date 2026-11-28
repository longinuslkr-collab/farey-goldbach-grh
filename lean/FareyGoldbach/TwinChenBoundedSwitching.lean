import FareyGoldbach.TwinChenSwitching

/-! # Removing the balanced semiprimes in the shifted-prime sequence -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem twin_bounded_or_balanced {X p r b L H y : ℕ} {α : ℝ}
    (hp : p∈twinChenRepresentations X r b) (hlarge : H<p+2) (hpy : y≤p)
    (hcut : ∀ {u v : ℕ}, H<u*v → u≤L → (u:ℝ)≤(v:ℝ)^(α-1)) :
    IsAlmostPrimeTwoBounded α (p+2) ∨ p∈chenSifted (2*r) y (twinChenAPBalancedB (X+3) r b L) := by
  obtain ⟨hp,hres,hm⟩ := mem_filter.mp hp
  obtain ⟨hpX,hp⟩ := Nat.mem_primesLE.mp hp
  rcases hm with h|h|⟨u,v,hu,hv,hm⟩
  · omega
  · exact Or.inl (Or.inl h)
  · have horder : ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ p+2=u*v ∧ u≤v := by
      rcases le_total u v with huv|hvu
      · exact ⟨u,v,hu,hv,hm,huv⟩
      · exact ⟨v,u,hv,hu,hm.trans (Nat.mul_comm ..),hvu⟩
    obtain ⟨u,v,hu,hv,hm,huv⟩ := horder
    by_cases hs : u≤L
    · exact Or.inl (Or.inr ⟨u,v,hu,hv,hm,hcut (hm ▸ hlarge) hs⟩)
    · right
      have hlt : u*v<X+3 := by omega
      have hup := (Nat.le_mul_of_pos_right u hv.pos).trans hlt.le
      have hvp := (Nat.le_mul_of_pos_left v hu.pos).trans hlt.le
      have hx : (u,v)∈chenBalancedPairs (X+3) L := mem_filter.mpr
        ⟨mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hup,hu⟩,Nat.mem_primesLE.mpr ⟨hvp,hv⟩⟩,
          lt_of_not_ge hs,huv,hlt⟩
      have hshift : u*v-2=p := by omega
      have hpr := (show p≡b [MOD r] from hres).add_right 2
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_image.mpr ⟨(u,v),hx,hshift⟩,hpr⟩,?_⟩
      intro q hq hqP _ hqd
      have hq₁ := mem_range.mp hq
      have hq₂ := (Nat.prime_dvd_prime_iff_eq hqP hp).mp hqd
      omega

theorem twinChen_representations_le_bounded_add_balanced {X r b L H y : ℕ} {α : ℝ}
    (hcut : ∀ {u v : ℕ}, H<u*v → u≤L → (u:ℝ)≤(v:ℝ)^(α-1)) :
    (twinChenRepresentations X r b).card ≤ (twinChenBoundedRepresentations X r b α).card+
      (chenSifted (2*r) y (twinChenAPBalancedB (X+3) r b L)).card+(H+1+y) := by
  let S := twinChenRepresentations X r b
  let B := chenSifted (2*r) y (twinChenAPBalancedB (X+3) r b L)
  have hcover (p : ℕ) (hp : p∈S) : 1 ≤
      ((if IsAlmostPrimeTwoBounded α (p+2) then 1 else 0) +
      (if p∈B then 1 else 0) + (if p+2≤H then 1 else 0) + (if p<y then 1 else 0) : ℕ) := by
    by_cases hs : p+2≤H
    · rw [ite_eq_left hs]; omega
    by_cases hpy : p<y
    · rw [ite_eq_left hpy]; omega
    rcases twin_bounded_or_balanced hp (lt_of_not_ge hs) (le_of_not_gt hpy) hcut with hg|hb
    · rw [ite_eq_left hg]; omega
    · rw [ite_eq_left (show p∈B from hb)]; omega
  have h := sum_le_sum (s:=S) hcover
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.sum_add_distrib,Finset.sum_boole,
    Nat.cast_id] at h
  have hbal : (S.filter (·∈B)).card≤B.card := card_le_card (fun _ hx => (mem_filter.mp hx).2)
  have hpr : (S.filter (·<y)).card≤y := by
    calc _ ≤ (range y).card := card_le_card (fun _ hx => mem_range.mpr (mem_filter.mp hx).2)
         _ = _ := card_range ..
  have hsm : (S.filter (fun p => p+2≤H)).card≤H+1 := by
    calc _ ≤ (range (H+1)).card := card_le_card (fun p hx => mem_range.mpr
           (by have hp : p+2≤H := (mem_filter.mp hx).2; omega))
         _ = _ := card_range ..
  have hgood : (S.filter (fun p => IsAlmostPrimeTwoBounded α (p+2))).card ≤
      (twinChenBoundedRepresentations X r b α).card := by
    refine card_le_card fun p hp => ?_
    obtain ⟨hp,hmore⟩ := mem_filter.mp hp
    obtain ⟨hp,hres,_⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hp,hres,hmore⟩
  change S.card≤_+B.card+(H+1+y)
  omega

theorem twinChen_bounded_switching_inequality {X r b : ℕ} {η εcut α : ℝ}
    (hM : 2^24≤X+3) (hb : (b+2).Coprime r)
    (_hη : 0<η) (_hη' : η<1/6) (_hε : 0<εcut) (hεη : εcut<η) (hα : 1<α)
    (hratio : (1/2-η)/(1/2+η-εcut)≤α-1) :
    let M := X+3
    let z := chenLowerCutoff M
    let y := chenUpperCutoff M
    let L := chenPowerLevel (1/2-η) M
    let H := chenPowerLevel (1-εcut) M
    ((chenSifted (2*r) z (twinChenAPA X r b)).card:ℝ) -
      (1/2:ℝ)*(∑ q∈chenMediumPrimes z y,
        ((chenSifted (2*r) z (chenDivisible (twinChenAPA X r b) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted (2*r) y (twinChenAPUnrestrictedB M r b z y)).card:ℝ) -
      (2*(M:ℝ)^(7/8:ℝ)+(M:ℝ)^(1/3:ℝ)) -
      ((chenSifted (2*r) y (twinChenAPBalancedB M r b L)).card:ℝ) -
      ((H:ℝ)+1+y) ≤ ((twinChenBoundedRepresentations X r b α).card:ℝ) := by
  let M := X+3
  let L := chenPowerLevel (1/2-η) M
  let H := chenPowerLevel (1-εcut) M
  let y := chenUpperCutoff M
  have hm : 1≤X+3 := by omega
  have hsplit := twinChen_representations_le_bounded_add_balanced (X:=X) (r:=r) (b:=b)
    (y:=y) (H:=H) (L:=L) (fun hp hu => chen_bounded_factor_of_cut hm hεη hα hratio hp hu)
  have hreal : ((twinChenRepresentations X r b).card:ℝ) ≤ ((twinChenBoundedRepresentations X r b α).card:ℝ)+
    ((chenSifted (2*r) y (twinChenAPBalancedB M r b L)).card:ℝ)+((H:ℝ)+1+y) := by
    exact_mod_cast hsplit
  have hclass := twinChen_switching_inequality hM hb
  dsimp only
  dsimp only [y,L,H,M] at hreal
  linarith only [hclass,hreal]

end FareyGoldbach
