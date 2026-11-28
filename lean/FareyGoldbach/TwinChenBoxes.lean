import FareyGoldbach.ChenBalancedBoxes
import FareyGoldbach.ChenAPSwitchingRemainder

/-! # The dyadic interval representations of the two switched product carriers -/

open Finset
open scoped Classical

namespace FareyGoldbach

private noncomputable def twinChenRowSum {q : ℕ} (M : ℕ) (row : ℕ→ℕ→ℕ→ℂ)
    (lo : ℕ→ℕ) (i k : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ m∈Finset.Icc 1 (chenSwitchBoxM i), row i k m*χ (m:ZMod q)*
    ∑ w∈Finset.Icc (lo m) (chenSwitchBoxHi M i m), chenSwitchBoxB k w*χ (w:ZMod q)

/-- A finite product carrier together with an exact representation by moving prime intervals. -/
structure TwinChenBoxSystem (M : ℕ) where
  pairs : Finset (ℕ×ℕ)
  cutoff : ℕ
  row : ℕ→ℕ→ℕ→ℂ
  lo : ℕ→ℕ
  inj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) pairs
  product : ∀ x∈pairs, 0<x.1*x.2 ∧ x.1*x.2≤M
  rough : ∀ x∈pairs, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → cutoff≤p
  rowBound : ∀ i k m, ‖row i k m‖≤1
  loPos : ∀ m, 1≤lo m
  loBound : ∀ i k m, row i k m≠0 → (M:ℝ)^(1/4:ℝ)+1≤(lo m:ℝ)
  boxShape : ∀ i,
    (1≤chenSwitchBoxW M i ∧ chenSwitchBoxW M i≤M ∧
      (chenSwitchBoxM i:ℝ)*(chenSwitchBoxW M i:ℝ)≤2*M ∧
      (chenSwitchBoxM i:ℝ)≤2*(M:ℝ)^(3/4:ℝ) ∧
      (chenSwitchBoxW M i:ℝ)≤2*(M:ℝ)^(3/4:ℝ)) ∨
    (∀ (q k : ℕ) (χ : DirichletCharacter ℂ q), twinChenRowSum M row lo i k χ=0)
  decompose : ∀ (q k : ℕ) (χ : DirichletCharacter ℂ q),
    (∑ x∈pairs, chenMaskedChar χ k x.1*chenMaskedChar χ k x.2) =
      ∑ i∈Finset.range (M.log2+1), twinChenRowSum M row lo i k χ

noncomputable def TwinChenBoxSystem.sum {M q : ℕ} (B : TwinChenBoxSystem M)
    (i k : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  twinChenRowSum M B.row B.lo i k χ

noncomputable def twinChenClassicBoxes (M : ℕ) (hM : 1≤M)
    (hy : (M:ℝ)^(1/4:ℝ)+1≤(chenUpperCutoff M:ℝ)) : TwinChenBoxSystem M where
  pairs := chenSwitchPairs M (chenLowerCutoff M) (chenUpperCutoff M)
  cutoff := chenLowerCutoff M
  row := chenSwitchBoxA (chenLowerCutoff M) (chenUpperCutoff M)
  lo := chenSwitchBoxLo
  inj := chenSwitchPairs_product_injective ..
  product := fun _ hx => ⟨chenSwitchPairs_product_pos hx,(chenSwitchPairs_product_lt hx).le⟩
  rough := fun _ hx _ hp hd => chenSwitchPairs_rough hx hp hd
  rowBound := chenSwitchBoxA_norm_le (chenLowerCutoff M) (chenUpperCutoff M)
  loPos := chenSwitchBoxLo_pos
  loBound := by
    intro i k m h
    have hs : chenSwitchBoxActive (chenLowerCutoff M) (chenUpperCutoff M) i m ∧ m.Coprime k := by
      by_contra hn
      exact h (ite_eq_right hn)
    exact hy.trans (Nat.cast_le.mpr (hs.1.2.2.2.2.2.trans (le_max_right ..)))
  boxShape := by
    intro i
    by_cases he : (chenSwitchBoxPairs M (chenLowerCutoff M) (chenUpperCutoff M) i).Nonempty
    · exact Or.inl (chenSwitchBox_ranges hy hM he)
    · exact Or.inr (fun _ _ χ => chenSwitchBoxSum_eq_zero_of_empty
        (Finset.not_nonempty_iff_eq_empty.mp he) χ)
  decompose := fun _ k χ => chenSwitch_masked_sum_eq_sum_boxes M _ _ k χ

noncomputable def twinChenBalancedBoxes (M L : ℕ) (hM : 1≤M)
    (hL : (M:ℝ)^(1/4:ℝ)+1≤(L:ℝ)) : TwinChenBoxSystem M where
  pairs := chenBalancedPairs M L
  cutoff := L
  row := chenBalancedBoxA L
  lo := chenBalancedBoxLo
  inj := chenBalancedPairs_product_injective ..
  product := fun _ hx => ⟨chenBalancedPairs_product_pos hx,(chenBalancedPairs_product_lt hx).le⟩
  rough := fun _ hx _ hp hd => (chenBalancedPairs_rough hx hp hd).le
  rowBound := chenBalancedBoxA_norm_le _
  loPos := chenBalancedBoxLo_pos
  loBound := by
    intro i k m h
    have hs : chenBalancedBoxActive L i m ∧ m.Coprime k := by
      by_contra hn
      exact h (ite_eq_right hn)
    exact hL.trans (Nat.cast_le.mpr (hs.1.2.1.le.trans (le_max_right ..)))
  boxShape := by
    intro i
    by_cases he : (chenBalancedBoxPairs M L i).Nonempty
    · exact Or.inl (chenBalancedBox_ranges hL hM he)
    · exact Or.inr (fun _ _ χ => chenBalancedBoxSum_eq_zero_of_empty
        (Finset.not_nonempty_iff_eq_empty.mp he) χ)
  decompose := fun _ k χ => chenBalanced_masked_sum_eq_sum_boxes M L k χ

theorem twinChenBox_conductors_le {M i k a D R : ℕ} (B : TwinChenBoxSystem M) {T : ℝ}
    (hM : 1≤M) (ha : 0<a) (hD : D≤M) (hR : 1≤R) (hT : 0≤T)
    (hsmall : ∀ q : ℕ, 2≤q → q<D → q≤R →
      ∀ χ : DirichletCharacter ℂ (a*q), χ.IsPrimitive → ‖B.sum i k χ‖≤T) :
    (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
      chenPrimitiveNorm (a*q) (B.sum i k)/(q:ℝ)) ≤ chenAPBoxBudget M a D R T := by
  apply chen_ap_box_conductors_of_bounds (fun _ => B.sum i k) hT ha hsmall
  rcases B.boxShape i with ⟨hW,hWM,hMW,hMe,hWe⟩ | hempty
  · exact chen_large_conductor_interval_multiple_bound a (chenSwitchBoxM i) (chenSwitchBoxW M i)
      D R M ha (B.row i k) (chenSwitchBoxB k) B.lo (chenSwitchBoxHi M i)
      hM hW hWM hD hR hMW hMe hWe (fun m _ => B.rowBound i k m)
      (fun w _ => chenSwitchBoxB_norm_le k w) (fun m _ => B.loPos m) (fun m _ => chenSwitchBoxHi_le M i m)
  · have he (q : ℕ) : chenPrimitiveNorm (a*q) (B.sum i k)=0 := by
      unfold chenPrimitiveNorm
      split_ifs <;> simp [TwinChenBoxSystem.sum,hempty]
    simp_rw [he,zero_div,Finset.sum_const_zero]
    positivity

end FareyGoldbach
