import FareyGoldbach.ChenBalancedPairs
import FareyGoldbach.ChenBalancedFactorCut

/-! # Removing the balanced semiprimes from Chen's finite switching inequality -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem bounded_or_balanced {N p r b₁ b₂ L M y : ℕ} {α : ℝ}
    (hp : p∈chenAPRepresentations N r b₁ b₂) (hlarge : M<N-p) (hM : 1≤M)
    (hpy : y≤p)
    (hcut : ∀ {u v : ℕ}, M<u*v → u≤L → (u:ℝ)≤(v:ℝ)^(α-1)) :
    IsAlmostPrimeTwoBounded α (N-p) ∨ p∈chenSifted (r*N) y (chenAPBalancedB N r b₂ L) := by
  obtain ⟨hglob,_,hres⟩ := mem_filter.mp hp
  obtain ⟨hpr,hprime,hm⟩ := mem_filter.mp hglob
  have hpN : p≤N := by simpa using mem_range.mp hpr
  rcases hm with h | h | ⟨u,v,hu,hv,hm⟩
  · omega
  · exact Or.inl (Or.inl h)
  · have horder : ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ N-p=u*v ∧ u≤v := by
      rcases le_total u v with huv|hvu
      · exact ⟨u,v,hu,hv,hm,huv⟩
      · exact ⟨v,u,hv,hu,hm.trans (Nat.mul_comm ..),hvu⟩
    obtain ⟨u,v,hu,hv,hm,huv⟩ := horder
    by_cases hs : u≤L
    · exact Or.inl (Or.inr ⟨u,v,hu,hv,hm,hcut (hm ▸ hlarge) hs⟩)
    · right
      have hpos := hprime.pos
      have hlt : u*v<N := by omega
      have hup : u≤N := (Nat.le_mul_of_pos_right u hv.pos).trans hlt.le
      have hvp : v≤N := (Nat.le_mul_of_pos_left v hu.pos).trans hlt.le
      have hx : (u,v)∈chenBalancedPairs N L := mem_filter.mpr
        ⟨mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hup,hu⟩,Nat.mem_primesLE.mpr ⟨hvp,hv⟩⟩,
          lt_of_not_ge hs,huv,hlt⟩
      have hrefl : N-u*v=p := by omega
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_image.mpr ⟨(u,v),hx,hrefl⟩,hres⟩,?_⟩
      intro q hq hqP _ hqd
      have hq₁ := mem_range.mp hq
      have hq₂ := (Nat.prime_dvd_prime_iff_eq hqP hprime).mp hqd
      omega

/-- Partition the original prime-or-semiprime representations. The initial
segment is counted after reflection, and the primes below the sifting cutoff
are counted directly. The switched balanced set has coefficient one. -/
theorem chenAP_representations_le_bounded_add_balanced {N r b₁ b₂ L M y : ℕ} {α : ℝ}
    (hM : 1≤M)
    (hcut : ∀ {u v : ℕ}, M<u*v → u≤L → (u:ℝ)≤(v:ℝ)^(α-1)) :
    (chenAPRepresentations N r b₁ b₂).card ≤
      (chenAPBoundedRepresentations N r b₁ b₂ α).card+
      (chenSifted (r*N) y (chenAPBalancedB N r b₂ L)).card+(M+1+y) := by
  let S := chenAPRepresentations N r b₁ b₂
  let B := chenSifted (r*N) y (chenAPBalancedB N r b₂ L)
  have hpN (p : ℕ) (hp : p∈S) : p≤N := by
    simpa using mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
  have hcover (p : ℕ) (hp : p∈S) : 1 ≤
      ((if IsAlmostPrimeTwoBounded α (N-p) then 1 else 0) +
      (if p∈B then 1 else 0) + (if N-p≤M then 1 else 0) + (if p<y then 1 else 0) : ℕ) := by
    by_cases hs : N-p≤M
    · rw [ite_eq_left hs]; omega
    by_cases hpy : p<y
    · rw [ite_eq_left hpy]; omega
    rcases bounded_or_balanced hp (lt_of_not_ge hs) hM (le_of_not_gt hpy) hcut with hg|hb
    · rw [ite_eq_left hg]; omega
    · rw [ite_eq_left (show p∈B from hb)]; omega
  have h := sum_le_sum (s:=S) hcover
  simp only [Finset.sum_const,smul_eq_mul,mul_one,Finset.sum_add_distrib,Finset.sum_boole,
    Nat.cast_id] at h
  have hbal : (S.filter (·∈B)).card≤B.card := card_le_card (fun _ hx => (mem_filter.mp hx).2)
  have hpr : (S.filter (·<y)).card≤y := by
    calc
      _ ≤ (range y).card := card_le_card (fun _ hx => mem_range.mpr (mem_filter.mp hx).2)
      _ = _ := card_range ..
  have hsm : (S.filter (fun p => N-p≤M)).card≤M+1 := by
    calc
      _ ≤ (range (M+1)).card := by
        apply card_le_card_of_injOn (fun p => N-p)
        · intro p hp
          apply mem_range.mpr
          change N-p<M+1
          exact Nat.lt_succ_of_le (mem_filter.mp hp).2
        · intro p hp q hq he
          have h₁ := hpN p (mem_filter.mp hp).1
          have h₂ := hpN q (mem_filter.mp hq).1
          change N-p=N-q at he
          omega
      _ = _ := card_range ..
  change S.card ≤ (S.filter (fun p => IsAlmostPrimeTwoBounded α (N-p))).card+B.card+(M+1+y)
  omega

/-- Chen's progression switching inequality with the balanced semiprime
sift and the two explicit finite losses. -/
theorem chen_ap_bounded_switching_inequality {N r b₁ b₂ : ℕ} {η εcut α : ℝ}
    (hN : 2^24≤N) (hb₂ : b₂.Coprime r) (hadm : N%r=(b₁+b₂)%r)
    (_hη : 0<η) (hη₆ : η<1/6) (_hε : 0<εcut) (hεη : εcut<η)
    (hα : 1<α) (hratio : (1/2-η)/(1/2+η-εcut)≤α-1) :
    let z := chenLowerCutoff N
    let y := chenUpperCutoff N
    let L := chenPowerLevel (1/2-η) N
    let M := chenPowerLevel (1-εcut) N
    ((chenSifted (r*N) z (chenAPA N r b₁)).card:ℝ) -
      (1/2:ℝ)*(∑ q∈chenMediumPrimes z y,
        ((chenSifted (r*N) z (chenDivisible (chenAPA N r b₁) q)).card:ℝ)) -
      (1/2:ℝ)*((chenSifted (r*N) y (chenAPUnrestrictedB N r b₂ z y)).card:ℝ) -
      (2*(N:ℝ)^(7/8:ℝ)+(N:ℝ)^(1/3:ℝ)) -
      ((chenSifted (r*N) y (chenAPBalancedB N r b₂ L)).card:ℝ) -
      ((M:ℝ)+1+y) ≤ ((chenAPBoundedRepresentations N r b₁ b₂ α).card:ℝ) := by
  have hNp : 1≤N := by omega
  have hM : 1≤chenPowerLevel (1-εcut) N := by
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_rpow (Nat.one_le_cast.mpr hNp) (by linarith only [hη₆,hεη])
  have hsplit := chenAP_representations_le_bounded_add_balanced
    (N:=N) (r:=r) (b₁:=b₁) (b₂:=b₂) (y:=chenUpperCutoff N) hM (fun hp hu =>
      chen_bounded_factor_of_cut hNp hεη hα hratio hp hu)
  have hreal : ((chenAPRepresentations N r b₁ b₂).card:ℝ) ≤
      ((chenAPBoundedRepresentations N r b₁ b₂ α).card:ℝ)+
      ((chenSifted (r*N) (chenUpperCutoff N)
        (chenAPBalancedB N r b₂ (chenPowerLevel (1/2-η) N))).card:ℝ)+
      ((chenPowerLevel (1-εcut) N:ℝ)+1+(chenUpperCutoff N:ℝ)) := by exact_mod_cast hsplit
  have hold := chenAP_switching_inequality_floor_explicit hN hb₂ hadm
  rw [chenAPCount_eq_representations_card hadm] at hold
  dsimp only
  linarith only [hold,hreal]

end FareyGoldbach
