import FareyGoldbach.ChenAPConductorExpansion
import FareyGoldbach.ChenAPDistributionInterfaces
import FareyGoldbach.ChenAPSwitchingFibers
import FareyGoldbach.ChenSwitchingPrincipal

/-! # The two-character expansion of the switched discrepancy in a fixed class -/

open Finset
open scoped Classical

namespace FareyGoldbach

private theorem ap_pair_twist_le (P : Finset (ℕ×ℕ)) {r d b : ℕ}
    [NeZero r] (hb : b.Coprime r) (η : DirichletCharacter ℂ d) :
    ‖∑ x∈P.filter (fun x => (x.1*x.2)%r=b%r), η ((x.1*x.2:ℕ):ZMod d)‖ ≤
      (∑ ψ : DirichletCharacter ℂ r,
        ‖∑ x∈P, ψ ((x.1*x.2:ℕ):ZMod r)*η ((x.1*x.2:ℕ):ZMod d)‖)/(r.totient:ℝ) := by
  let E (x : ℕ×ℕ) := η ((x.1*x.2:ℕ):ZMod d)
  have hb' := (ZMod.isUnit_iff_coprime b r).mpr hb
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos r))
  have hid : (∑ ψ : DirichletCharacter ℂ r, ψ (b:ZMod r)⁻¹ *
      ∑ x∈P, ψ ((x.1*x.2:ℕ):ZMod r)*E x) =
      (r.totient:ℂ)*(∑ x∈P.filter (fun x => (x.1*x.2)%r=b%r), E x) := by
    simp_rw [Finset.mul_sum,← mul_assoc]
    rw [Finset.sum_comm, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_mul, DirichletCharacter.sum_char_inv_mul_char_eq ℂ hb']
    by_cases h : (x.1*x.2)%r=b%r
    · rw [ite_eq_left h,ite_eq_left ((ZMod.natCast_eq_natCast_iff' b _ r).2 h.symm)]
    · have hn : (b:ZMod r) ≠ ((x.1*x.2:ℕ):ZMod r) :=
        fun hz => h ((ZMod.natCast_eq_natCast_iff' b _ r).1 hz).symm
      rw [ite_eq_right h,ite_eq_right hn,zero_mul]
  apply (le_div_iff₀ hφ).mpr
  rw [mul_comm, ← Complex.norm_natCast, ← norm_mul, ← hid]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ψ _ => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (ψ.norm_le_one _)

private theorem ap_pair_discrepancy (P : Finset (ℕ×ℕ)) {r d b n : ℕ}
    [NeZero r] [NeZero d] (hb : b.Coprime r) (hn : n.Coprime d)
    (hrd : r.Coprime d) :
    let A := P.filter (fun x => (x.1*x.2)%r=b%r)
    |((A.filter (fun x => (x.1*x.2)%d=n%d)).card:ℝ)-(A.card:ℝ)/(d.totient:ℝ)| ≤
      ((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ)/(d.totient:ℝ) +
      (1/(r.totient:ℝ))*((∑ a∈r.divisors, ∑ q∈d.divisors.filter (fun q => 1<q),
        chenMaskedPrimitiveMass P (a*q) ((r/a)*(d/q)))/(d.totient:ℝ)) := by
  let A := P.filter (fun x => (x.1*x.2)%r=b%r)
  have hbad : ((A.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ) ≤
      ((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter (fun x : ℕ×ℕ => ¬(x.1*x.2).Coprime d) (Finset.filter_subset ..))
  have hsum := Finset.sum_le_sum (s:=(univ : Finset (DirichletCharacter ℂ d)).filter (·≠1))
    (fun η _ => ap_pair_twist_le P hb η)
  rw [← Finset.sum_div, Finset.sum_comm] at hsum
  have htw := chenAP_twisted_conductor_sum_le P hrd
  refine (chenPairAP_discrepancy_le_raw A (NeZero.pos d) hn).trans ?_
  rw [add_div]
  refine add_le_add (div_le_div_of_nonneg_right hbad (by positivity)) ?_
  have h := div_le_div_of_nonneg_right (hsum.trans
    (div_le_div_of_nonneg_right htw (by positivity))) (Nat.cast_nonneg (α:=ℝ) (d.totient))
  simpa only [div_eq_mul_inv, one_mul, mul_left_comm, mul_comm, mul_assoc] using h

/-- Expanding both residue conditions and grouping by primitive conductor
works for any finite carrier with distinct rough products. -/
theorem chenAP_pair_error_le_conductors_at {N r b D z K t : ℕ} (hN : 1≤N) (hr : 0<r)
    (hz : 0<z) (hD : D≤N) (hKr : r∣K) (hKt : t∣K) (hb : b.Coprime r) (P : Finset (ℕ×ℕ)) (err : ℕ→ℝ)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N)
    (hrough : ∀ x∈P, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p)
    (herr : ∀ d, let A := P.filter (fun x => (x.1*x.2)%r=b%r)
      err d = ((A.filter (fun x => (x.1*x.2)%d=t%d)).card:ℝ)-(A.card:ℝ)/(d.totient:ℝ)) :
    chenReducedError K D err ≤
      4*(chenSwitchLog N)^3*((N:ℝ)/(z:ℝ)) +
      (1/(r.totient:ℝ))*∑ a∈r.divisors, ∑ k∈Finset.Ico 1 D, (1/(k.totient:ℝ))*
        ∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
          chenMaskedPrimitiveMass P (a*q) ((r/a)*k)/(q.totient:ℝ) := by
  let S := (Finset.Ico 1 D).filter (fun d => d.Coprime K)
  let G (d : ℕ) := ((P.filter (fun x => ¬(x.1*x.2).Coprime d)).card:ℝ)/(d.totient:ℝ)
  let E (a q k : ℕ) := chenMaskedPrimitiveMass P (a*q) ((r/a)*k)
  let F (d : ℕ) := (∑ a∈r.divisors, ∑ q∈d.divisors.filter (fun q => 1<q), E a q (d/q))/(d.totient:ℝ)
  let _ : NeZero r := ⟨hr.ne'⟩
  have hdK {d : ℕ} (hd : d∈S) : d.Coprime K := (Finset.mem_filter.mp hd).2
  have hS : S ⊆ (Finset.Ico 1 D).filter (fun d => d.Coprime (r*1)) := by
    intro d hd
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,
      by simpa only [Nat.mul_one] using (hdK hd).coprime_dvd_right hKr⟩
  have hG : (∑ d∈S, G d) ≤ 4*(chenSwitchLog N)^3*((N:ℝ)/(z:ℝ)) :=
    chenPair_principal_correction_for P hN hz hD S (Finset.filter_subset ..) hinj hprod hrough
  have hF := chenAP_conductor_reindex r 1 D E (fun a q k => chenMaskedPrimitiveMass_nonneg P _ _)
  have hF' := (Finset.sum_le_sum_of_subset_of_nonneg hS
    (fun _ _ _ => div_nonneg (Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => chenMaskedPrimitiveMass_nonneg P _ _) (by positivity))).trans hF

  change (∑ d∈S, |err d|) ≤ _
  calc
    _ ≤ ∑ d∈S, (G d + (1/(r.totient:ℝ))*F d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdp := (Finset.mem_Ico.mp (Finset.mem_filter.mp hd).1).1
      have hdr := (hdK hd).coprime_dvd_right hKr
      have hdn := (hdK hd).coprime_dvd_right hKt
      let _ : NeZero d := ⟨by omega⟩
      rw [herr d]; exact ap_pair_discrepancy P hb hdn.symm hdr.symm

    _ = (∑ d∈S,G d)+(1/(r.totient:ℝ))*∑ d∈S,F d := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := add_le_add hG (mul_le_mul_of_nonneg_left hF' (by positivity))


theorem chenAP_pair_error_le_conductors {N r b D z : ℕ} (hN : 1≤N) (hr : 0<r)
    (hz : 0<z) (hD : D≤N) (hb : b.Coprime r) (P : Finset (ℕ×ℕ)) (err : ℕ→ℝ)
    (hinj : Set.InjOn (fun x : ℕ×ℕ => x.1*x.2) P)
    (hprod : ∀ x∈P, 0<x.1*x.2 ∧ x.1*x.2≤N)
    (hrough : ∀ x∈P, ∀ p : ℕ, p.Prime → p∣x.1*x.2 → z≤p)
    (herr : ∀ d, let A := P.filter (fun x => (x.1*x.2)%r=b%r)
      err d = ((A.filter (fun x => (x.1*x.2)%d=N%d)).card:ℝ)-(A.card:ℝ)/(d.totient:ℝ)) :
    chenReducedError (r*N) D err ≤
      4*(chenSwitchLog N)^3*((N:ℝ)/(z:ℝ)) +
      (1/(r.totient:ℝ))*∑ a∈r.divisors, ∑ k∈Finset.Ico 1 D, (1/(k.totient:ℝ))*
        ∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
          chenMaskedPrimitiveMass P (a*q) ((r/a)*k)/(q.totient:ℝ) :=
  chenAP_pair_error_le_conductors_at hN hr hz hD (Nat.dvd_mul_right r N)
    (Nat.dvd_mul_left N r) hb P err hinj hprod hrough herr

/-- The principal term is bounded by the unfiltered switched sequence. The
remaining terms are organized by the two primitive conductors. -/
theorem chenAP_switching_error_le_conductors {N r b D : ℕ} (hN : 1≤N) (hr : 0<r)
    (hz : 0<chenLowerCutoff N) (hD : D≤N) (hb : b.Coprime r) :
    let P := chenSwitchPairs N (chenLowerCutoff N) (chenUpperCutoff N)
    chenReducedError (r*N) D (chenAPSwitchedError N r b) ≤
      4*(chenSwitchLog N)^3*((N:ℝ)/(chenLowerCutoff N:ℝ)) +
      (1/(r.totient:ℝ))*∑ a∈r.divisors, ∑ k∈Finset.Ico 1 D, (1/(k.totient:ℝ))*
        ∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
          chenMaskedPrimitiveMass P (a*q) ((r/a)*k)/(q.totient:ℝ) := by
  dsimp only
  let z := chenLowerCutoff N
  let y := chenUpperCutoff N
  let P := chenSwitchPairs N z y
  apply chenAP_pair_error_le_conductors hN hr hz hD hb P (chenAPSwitchedError N r b)
    (chenSwitchPairs_product_injective N z y)
    (fun _ hx => ⟨chenSwitchPairs_product_pos hx,(chenSwitchPairs_product_lt hx).le⟩)
    (fun _ hx _ hp hd => chenSwitchPairs_rough hx hp hd)
  intro d
  simp only [chenAPSwitchedError,chenAPError,chenAPUnrestrictedB_card_eq_pair_filter,
    chenAPUnrestrictedB_card_divisible_pair_filter,P,z,y,Finset.filter_filter]

end FareyGoldbach
