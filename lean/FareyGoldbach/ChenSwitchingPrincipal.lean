import FareyGoldbach.ChenSwitchingScales

/-! # The principal-character correction for switched products -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem chenPair_divides_card_le (P : Finset (ℕ×ℕ)) {N p : ℕ}
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N) :
    (P.filter fun x => p∣x.1*x.2).card ≤ N/p := by
  let S := P.filter fun x => p∣x.1*x.2
  let f (x : ℕ×ℕ) := x.1*x.2/p
  have hS (x : ℕ×ℕ) (hx : x∈S) : x∈P ∧ f x*p=x.1*x.2 :=
    ⟨(Finset.mem_filter.mp hx).1,Nat.div_mul_cancel (Finset.mem_filter.mp hx).2⟩
  have he : Set.InjOn f S := by
    intro x hx y hy hxy
    exact hinj (hS x hx).1 (hS y hy).1 (by
      change x.1*x.2=y.1*y.2
      rw [←(hS x hx).2,←(hS y hy).2,hxy])
  have hi : S.image f ⊆ Finset.Icc 1 (N/p) := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    have hx' := hprod x (hS x hx).1
    have hz : f x≠0 := fun h => by
      have hh := (hS x hx).2
      rw [h,zero_mul] at hh
      exact (Nat.ne_of_gt hx'.1) hh.symm
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hz,Nat.div_le_div_right hx'.2⟩
  calc S.card = (S.image f).card := (Finset.card_image_of_injOn he).symm
    _ ≤ (Finset.Icc 1 (N/p)).card := Finset.card_le_card hi
    _ = _ := by simp

theorem chenPair_nonCoprime_card_le (P : Finset (ℕ×ℕ)) {N z d : ℕ}
    (hz : 0<z) (hd : 0<d)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N)
    (hrough : ∀ x∈P, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p) :
    ((P.filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)≤
      (d.primeFactors.card:ℝ)*((N:ℝ)/z) := by
  let S := fun p : ℕ => P.filter fun x => p∣x.1*x.2
  let U := d.primeFactors
  let E := P.filter fun x => ¬(x.1*x.2).Coprime d
  have hcover : E ⊆ U.biUnion S := by
    intro x hx
    obtain ⟨hp,hc⟩ := Finset.mem_filter.mp hx
    let g := (x.1*x.2).gcd d
    have hg : g≠1 := hc
    let p := g.minFac
    have hpp : p.Prime := Nat.minFac_prime hg
    have hp₁ : p∣x.1*x.2 := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_left ..)
    have hp₂ : p∣d := (Nat.minFac_dvd g).trans (Nat.gcd_dvd_right ..)
    exact Finset.mem_biUnion.mpr
      ⟨p,Nat.mem_primeFactors.mpr ⟨hpp,hp₂,hd.ne'⟩,Finset.mem_filter.mpr ⟨hp,hp₁⟩⟩
  have hcard (p : ℕ) (hp : p∈U) : ((S p).card:ℝ)≤(N:ℝ)/z := by
    have hpp := Nat.prime_of_mem_primeFactors hp
    by_cases hpz : z≤p
    · have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hpp.pos
      have hz' : (0:ℝ)<z := Nat.cast_pos.mpr hz
      calc _ ≤ ((N/p:ℕ):ℝ) := Nat.cast_le.mpr (chenPair_divides_card_le P hinj hprod)
        _ ≤ (N:ℝ)/p := by
          apply (le_div_iff₀ hp').2
          exact_mod_cast Nat.div_mul_le_self N p
        _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hz' (Nat.cast_le.mpr hpz)
    · have hzero : S p=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
        obtain ⟨hx',hd'⟩ := Finset.mem_filter.mp hx
        exact hpz (hrough x hx' p hpp hd')
      rw [hzero]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  calc (E.card:ℝ) ≤ ((U.biUnion S).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ p∈U, ((S p).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p∈U, (N:ℝ)/z := Finset.sum_le_sum hcard
    _ = _ := by simp [U]

theorem chenPair_principal_correction_for (P : Finset (ℕ×ℕ)) {N z D : ℕ}
    (hN : 1≤N) (hz : 0<z) (hD : D≤N) (R : Finset ℕ) (hR₀ : R⊆Finset.Ico 1 D)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N)
    (hrough : ∀ x∈P, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p) :
    (∑ d ∈ R,
      ((P.filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)/(d.totient:ℝ))≤
        4*(chenSwitchLog N)^3*((N:ℝ)/z) := by
  let L := chenSwitchLog N
  have hL : 0≤L := zero_le_one.trans (one_le_chenSwitchLog hN)
  have hR : R⊆Finset.Icc 1 N := fun d hd => by
    obtain ⟨h₁,h₂⟩ := Finset.mem_Ico.mp (hR₀ hd)
    exact Finset.mem_Icc.mpr ⟨h₁,h₂.le.trans hD⟩
  have hf (d : ℕ) (hd : d∈R) : ((P.filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)≤
      (2*L)*((N:ℝ)/z) := by
    obtain ⟨hp,hu⟩ := Finset.mem_Icc.mp (hR hd)
    apply (chenPair_nonCoprime_card_le P hz hp hinj hprod hrough).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hp' : (0:ℝ)<d := Nat.cast_pos.mpr hp
    have hlog := Real.log_le_log (by positivity : 0<2*(d:ℝ))
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hu) (by norm_num : (0:ℝ)≤2))
    exact (primeFactors_card_le_two_log hp).trans (by dsimp [L,chenSwitchLog]; linarith only [hlog])
  calc _ ≤ ∑ d∈R, ((2*L)*((N:ℝ)/z))*(1/(d.totient:ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          simpa only [div_eq_mul_inv,one_mul] using
            mul_le_mul_of_nonneg_right (hf d hd) (by positivity : 0≤(1/(d.totient:ℝ)))
    _ = ((2*L)*((N:ℝ)/z))*(∑ d∈R, 1/(d.totient:ℝ)) := by rw [Finset.mul_sum]
    _ ≤ ((2*L)*((N:ℝ)/z))*(2*L^2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => by positivity)).trans
            (chen_sum_inv_totient_le hN)
    _ = _ := by dsimp only [L]; ring

theorem chenPair_principal_correction (P : Finset (ℕ×ℕ)) {N z D : ℕ}
    (hN : 1≤N) (hz : 0<z) (hD : D≤N)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N)
    (hrough : ∀ x∈P, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p) :
    (∑ d ∈ (Finset.Ico 1 D).filter (fun d => d.Coprime N),
      ((P.filter fun x => ¬(x.1*x.2).Coprime d).card:ℝ)/(d.totient:ℝ))≤
        4*(chenSwitchLog N)^3*((N:ℝ)/z) :=
  chenPair_principal_correction_for P hN hz hD _ (Finset.filter_subset ..) hinj hprod hrough

end FareyGoldbach
