import FareyGoldbach.TwinChenBoxes
import FareyGoldbach.TwinChenDistributionInterfaces
import FareyGoldbach.ChenBalancedRemainderCore

/-! # Character expansion of divisor errors at the target residue two -/

open Filter Finset
open scoped Classical

namespace FareyGoldbach

def TwinChenCarrierHasBoxes (carrier : ℕ→ℕ→ℕ→Finset ℕ) : Prop :=
  ∀ᶠ M : ℕ in atTop, ∃ B : TwinChenBoxSystem M,
    (M:ℝ)^(1/16:ℝ)+1≤(B.cutoff:ℝ) ∧ ∀ (r b d : ℕ),
      let A := B.pairs.filter (fun x => (x.1*x.2)%r=(b+2)%r)
      chenAPError (carrier M r b) (carrier M r b).card d =
        ((A.filter (fun x => (x.1*x.2)%d=2%d)).card:ℝ)-(A.card:ℝ)/(d.totient:ℝ)

theorem twinChenClassicCarrier_hasBoxes : TwinChenCarrierHasBoxes twinChenClassicCarrier := by
  filter_upwards [chenSwitching_cutoffs_eventually,eventually_ge_atTop (1:ℕ)] with M hcut hM
  refine ⟨twinChenClassicBoxes M hM hcut.1,hcut.2,?_⟩
  intro r b d
  simp only [twinChenClassicCarrier,chenAPError,twinChenClassicBoxes,
    twinChenAPUnrestrictedB_card_eq_pair_filter,twinChenAPUnrestrictedB_card_divisible_pair_filter,
    Finset.filter_filter]

theorem twinChenBoundedCarrier_hasBoxes {η : ℝ} (hη : η<1/6) :
    TwinChenCarrierHasBoxes (twinChenBoundedCarrier η) := by
  filter_upwards [chen_balanced_cutoff_eventually hη,eventually_ge_atTop (1:ℕ)] with M hcut hM
  have hh : (M:ℝ)^(1/16:ℝ)≤(M:ℝ)^(1/4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hM) (by norm_num)
  refine ⟨twinChenBalancedBoxes M _ hM hcut,(add_le_add hh le_rfl).trans hcut,?_⟩
  intro r b d
  simp only [twinChenBoundedCarrier,chenAPError,twinChenBalancedBoxes,
    twinChenAPBalancedB_card_eq_pair_filter,twinChenAPBalancedB_card_divisible_pair_filter,
    Finset.filter_filter]

theorem twinChen_error_le_of_boxes {M r b D : ℕ} (B : TwinChenBoxSystem M) (err : ℕ→ℝ)
    (hM : 1≤M) (hr : 0<r) (hz : 0<B.cutoff) (hD : D≤M) (hb : (b+2).Coprime r)
    (herr : ∀ d, let A := B.pairs.filter (fun x => (x.1*x.2)%r=(b+2)%r)
      err d = ((A.filter (fun x => (x.1*x.2)%d=2%d)).card:ℝ)-(A.card:ℝ)/(d.totient:ℝ))
    {J : ℕ→ℝ} (hJ : ∀ a∈r.divisors, 0≤J a)
    (hbox : ∀ a∈r.divisors, ∀ k∈Finset.Ico 1 D, ∀ i∈Finset.range (M.log2+1),
      (∑ q∈(Finset.Ico 2 D).filter (fun q => a.Coprime q),
        chenPrimitiveNorm (a*q) (B.sum i ((r/a)*k))/(q:ℝ))≤J a) :
    (r.totient:ℝ)*chenReducedError (2*r) D err ≤
      (r.totient:ℝ)*(4*(chenSwitchLog M)^3*((M:ℝ)/(B.cutoff:ℝ))) +
      6*(chenSwitchLog M)^3*∑ a∈r.divisors,J a := by
  have hφ : (0:ℝ)<r.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hr)
  have ht := chenAP_pair_error_le_conductors_at hM hr hz hD
    (Nat.dvd_mul_left r 2) (Nat.dvd_mul_right 2 r) hb B.pairs err B.inj B.product B.rough herr
  have hs := chen_ap_pair_box_weights_le hM hr hD B.pairs (fun _ i k => B.sum i k) B.decompose hJ hbox
  have hh := mul_le_mul_of_nonneg_left ht hφ.le
  rw [mul_add] at hh
  have hcancel : (r.totient:ℝ)*(1/(r.totient:ℝ))=1 := by field_simp
  rw [←mul_assoc (r.totient:ℝ) (1/(r.totient:ℝ)),hcancel,one_mul] at hh
  exact hh.trans (add_le_add le_rfl hs)

end FareyGoldbach
