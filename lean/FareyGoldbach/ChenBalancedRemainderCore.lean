import FareyGoldbach.ChenBalancedBoxes
import FareyGoldbach.ChenAPSwitchingRemainder

/-! # Conductor bounds for the balanced prime-pair carrier -/

open Finset
open scoped Classical

namespace FareyGoldbach

noncomputable def chenAPBalancedError (N r b L d : ℕ) : ℝ :=
  chenAPError (chenAPBalancedB N r b L) (chenAPBalancedB N r b L).card d

theorem chenAPBalancedB_modulus_one (N b L : ℕ) :
    chenAPBalancedB N 1 b L=chenBalancedB N L := by simp [chenAPBalancedB,Nat.mod_one]

theorem chen_balanced_box_conductors_le {N L i K a D R : ℕ} {B : ℝ}
    (hN : 1≤N) (hL : (N:ℝ)^(1/4:ℝ)+1≤(L:ℝ)) (ha : 0<a) (hD : D≤N) (hR : 1≤R)
    (hB : 0≤B)
    (hsmall : ∀ q : ℕ, 2≤q → q<D → q≤R →
      ∀ χ : DirichletCharacter ℂ (a*q), χ.IsPrimitive →
        ‖chenBalancedBoxSum N L i K χ‖≤B) :
    (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
      chenPrimitiveNorm (a*q) (chenBalancedBoxSum N L i K)/(q:ℝ))≤
        chenAPBoxBudget N a D R B := by
  apply chen_ap_box_conductors_of_bounds (fun _ => chenBalancedBoxSum N L i K) hB ha hsmall
  by_cases hne : (chenBalancedBoxPairs N L i).Nonempty
  · obtain ⟨hW,hWN,hMW,hM,hWpow⟩ := chenBalancedBox_ranges hL hN hne
    have heq (q : ℕ) : (chenBalancedBoxSum N L i K : DirichletCharacter ℂ q→ℂ) =
        fun χ => ∑ m∈Finset.Icc 1 (chenSwitchBoxM i), chenBalancedBoxA L i K m*χ (m:ZMod q)*
          ∑ w∈Finset.Icc (chenBalancedBoxLo m) (chenSwitchBoxHi N i m),
            chenSwitchBoxB K w*χ (w:ZMod q) := rfl
    simp_rw [heq]
    exact chen_large_conductor_interval_multiple_bound a (chenSwitchBoxM i) (chenSwitchBoxW N i)
      D R N ha (chenBalancedBoxA L i K) (chenSwitchBoxB K) chenBalancedBoxLo (chenSwitchBoxHi N i)
      hN hW hWN hD hR hMW hM hWpow
      (fun m _ => chenBalancedBoxA_norm_le L i K m) (fun w _ => chenSwitchBoxB_norm_le K w)
      (fun m _ => chenBalancedBoxLo_pos m) (fun m _ => chenSwitchBoxHi_le N i m)
  · have hz (q : ℕ) : chenPrimitiveNorm (a*q) (chenBalancedBoxSum N L i K)=0 := by
      unfold chenPrimitiveNorm
      split_ifs <;> simp [chenBalancedBoxSum_eq_zero_of_empty
        (Finset.not_nonempty_iff_eq_empty.mp hne)]
    simp_rw [hz,zero_div,Finset.sum_const_zero]
    positivity

theorem chen_balanced_remainder_of_box_bounds {N r b L D : ℕ}
    (hN : 1≤N) (hr : 0<r) (hL : 0<L) (hD : D≤N) (hb : b.Coprime r)
    {J : ℕ→ℝ} (hJ : ∀ a∈r.divisors, 0≤J a)
    (hbox : ∀ a∈r.divisors, ∀ k∈Finset.Ico 1 D, ∀ i∈Finset.range (N.log2+1),
      (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenPrimitiveNorm (a*q) (chenBalancedBoxSum N L i ((r/a)*k))/(q:ℝ))≤J a) :
    (r.totient:ℝ)*chenReducedError (r*N) D (chenAPBalancedError N r b L) ≤
      (r.totient:ℝ)*(4*(chenSwitchLog N)^3*((N:ℝ)/(L:ℝ))) +
      6*(chenSwitchLog N)^3*∑ a∈r.divisors,J a := by
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have hdis := chenAP_pair_error_le_conductors hN hr hL hD hb
    (chenBalancedPairs N L) (chenAPBalancedError N r b L)
    (chenBalancedPairs_product_injective N L)
    (fun _ hx => ⟨chenBalancedPairs_product_pos hx,(chenBalancedPairs_product_lt hx).le⟩)
    (fun _ hx _ hp hd => (chenBalancedPairs_rough hx hp hd).le)
    (by intro d; simp only [chenAPBalancedError,chenAPError,
      chenAPBalancedB_card_eq_pair_filter,chenAPBalancedB_card_divisible_pair_filter,Finset.filter_filter])
  have hsum := chen_ap_pair_box_weights_le hN hr hD (chenBalancedPairs N L)
    (fun _ i k => chenBalancedBoxSum N L i k)
    (fun _ k χ => chenBalanced_masked_sum_eq_sum_boxes N L k χ) hJ hbox
  have hh := mul_le_mul_of_nonneg_left hdis hφ.le
  rw [mul_add] at hh
  have hcancel : (r.totient:ℝ)*(1/(r.totient:ℝ))=1 := by field_simp
  rw [←mul_assoc (r.totient:ℝ) (1/(r.totient:ℝ)),hcancel,one_mul] at hh
  exact hh.trans (add_le_add le_rfl hsum)

theorem chen_balanced_cutoff_eventually {η : ℝ} (hη : η<1/6) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (N:ℝ)^(1/4:ℝ)+1≤(chenPowerLevel (1/2-η) N:ℝ) :=
  eventually_rpow_add_one_le_powerLevel (by norm_num) (by linarith only [hη])

end FareyGoldbach
